// ==UserScript==
// @name         Steam Wishlist Lowest Value
// @namespace    http://tampermonkey.net/
// @version      4.0
// @description  Shows three totals for your wishlist in Steam's native controls bar: minimum value (Steam's real prices via IStoreBrowseService/GetItems like AugmentedSteam, compared with AllKeyShop's lowest offer), current value and original value, plus wishlist stats. Prices come from IStoreBrowseService/GetItems (protobuf, no scrolling) with appdetails/DOM as fallback; DOM scraping is passive only.
// @author       Menosuno02
// @match        https://store.steampowered.com/wishlist/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=steampowered.com
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      www.allkeyshop.com
// @connect      api.steampowered.com
// @connect      store.steampowered.com
// @run-at       document-idle
// ==/UserScript==

(function () {
    "use strict";

    // Last-resort steamid if the page doesn't expose one (leave empty to
    // disable and fall back to DOM mode). Usually the id comes from the URL
    // (/wishlist/profiles/<id>), the page's SSR state (vanity URLs of any
    // wishlist) or the logged-in user's data (see resolveSteamId).
    const DEFAULT_STEAMID = "";

    // Country/language — now detected dynamically (see getStoreCountry/getStoreLanguage).
    // Fallback kept for very early init before DOM is ready.
    const FALLBACK_CC = "es";
    const FALLBACK_LANG = "spanish";
    const WISHLIST_API_URL =
        "https://api.steampowered.com/IWishlistService/GetWishlist/v1/";
    const APPDETAILS_URL = "https://store.steampowered.com/api/appdetails";
    // appdetails / StoreBrowse accept many appids per call, but batch to stay under URL length limits.
    const PRICE_BATCH_SIZE = 50;
    const STORE_BROWSE_BATCH_SIZE = 50; // same as AugmentedSteam Zd
    // Timeout/retries for Steam calls (their weak point).
    const STEAM_TIMEOUT_MS = 15000;
    const STEAM_RETRY_DELAY_MS = 2000;
    // Names use one basic call per appid, at this concurrency.
    const NAME_FETCH_CONCURRENCY = 2;

    // How long a price stays "fresh" before re-fetching / no longer counting as recent.
    const MAX_AGE_MS = 24 * 60 * 60 * 1000; // 1 day

    const POLL_INTERVAL_MS = 100;

    // Delay between AllKeyShop API calls (undocumented endpoint; raise if
    // blocked, lower if in a hurry).
    const AKS_REQUEST_DELAY_MS = 45;
    // Failed requests retry sooner (5 min) — likely a temporary block.
    const AKS_ERROR_RETRY_MS = 5 * 60 * 1000; // 5 min
    const AKS_API_URL =
        "https://www.allkeyshop.com/api/v2-1-250304/vakrs_extension.php";
    const AKS_STATIC_PARAMS =
        "action=CatalogV2&sort_field=relevance&sort_order=desc&pagenum=1&per_page=1" +
        "&type=game+dlc&locale=en&price_mode=price_card&currency=eur" +
        "&fields=link,offers_count,operating_system.id,offers.price,offers.buy_url," +
        "offers.stock_status,offers.region.name,offers.edition.name,name" +
        "&operating_systems=pc";

    let currencySymbol = "€";
    let store = {};
    let storageKey = null;
    let apiMode = false; // API responded successfully
    let apiWishlistTotal = null; // wishlist size per API (coverage)
    let domModeStarted = false; // only started if the API fails
    // True while an API refresh is in flight: panels can be stale on a
    // long-open tab, so price capture from the DOM waits until the API pass
    // has stamped fresh entries (apiTs) or definitively failed.
    let domCaptureSuppressed = false;
    const sessionSeenIds = new Set();
    const pendingAksFetch = new Set();
    const aksQueue = [];
    let aksQueueBusy = false;
    const pendingNameFetch = new Set();
    const nameQueue = [];
    let nameQueueActive = 0;

    // ---------- Diagnostics ----------
    // All diagnostic output uses the [WMP] prefix so it can be filtered in
    // the console. domSnapshot is session-only and never persisted: what
    // each scanned panel actually rendered (price tag, discount badge) —
    // the same ground truth AugmentedSteam counts from.
    const SCRIPT_VERSION =
        typeof GM_info !== "undefined" && GM_info.script
            ? GM_info.script.version
            : "?";
    const domSnapshot = new Map(); // appid -> { tag, badge, seen }
    let verboseCapture = false;
    function log(...args) {
        console.log("[WMP]", ...args);
    }

    // ---------- Cache loading ----------
    // Cache per steamid when known (independent of the exact URL); by
    // pathname otherwise.
    function getStorageKey(steamid) {
        return steamid
            ? "wishlistMinPrices::api::" + steamid
            : "wishlistMinPrices::" + location.pathname;
    }

    function loadStore() {
        try {
            store = JSON.parse(GM_getValue(storageKey, "{}")) || {};
        } catch (e) {
            store = {};
        }
    }

    function persistStore() {
        try {
            GM_setValue(storageKey, JSON.stringify(store));
        } catch (e) {
            console.warn("[WishlistMinPrice] Could not save the cache", e);
        }
    }

    function resetCache({ reload = true } = {}) {
        // Drop prices but keep names, then trigger a full refresh.
        Object.keys(store).forEach((id) => {
            const { name, is_free } = store[id];
            store[id] = {};
            if (name) store[id].name = name;
            if (typeof is_free === "boolean") store[id].is_free = is_free;
        });
        pendingAksFetch.clear();
        aksQueue.length = 0;
        pendingNameFetch.clear();
        nameQueue.length = 0;
        domSnapshot.clear();
        persistStore();
        log(`resetCache: cleared entries (names kept, key=${storageKey}, left=${Object.keys(store).length})`);

        const steamid = resolveSteamId();
        if (steamid && reload) {
            // The in-place pass can pick up stale panel prices for items the
            // APIs miss (panels were rendered at page load, hours ago). A
            // fresh page re-renders everything with current data — init()
            // then runs the full refresh. This is the path that shows the
            // right totals (verified on manual reload).
            log("reset: reloading the page to refresh with clean data");
            setTimeout(() => {
                location.reload();
            }, 80);
        } else if (steamid) {
            refreshFromApi(steamid);
        } else {
            startDomMode();
            tryInject();
        }
    }

    // Exposed on unsafeWindow (not window): with @grant GM_*, the script
    // runs in a sandbox, so "window" there isn't the page's real window.
    unsafeWindow.__wishlistMinPriceReset = resetCache;

    // Debug: __wishlistMinPriceDebug() logs the N entries with the highest
    // "price" (default 20), with steamPrice/aksPrice separated.
    unsafeWindow.__wishlistMinPriceDebug = function (limit = 20) {
        const rows = Object.entries(store).map(([appid, v]) => ({
            appid,
            name: v.name || "(no name)",
            steamPrice: typeof v.steamPrice === "number" ? v.steamPrice : null,
            steamOriginal:
                typeof v.steamOriginalPrice === "number"
                    ? v.steamOriginalPrice
                    : null,
            discount:
                typeof v.discountPercent === "number" ? v.discountPercent : null,
            noPrice: v.noPrice === true,
            aksPrice: typeof v.aksPrice === "number" ? v.aksPrice : null,
            price: typeof v.price === "number" ? v.price : null,
            ts: v.ts ? new Date(v.ts).toLocaleString() : null,
        }));
        rows.sort((a, b) => (b.price || 0) - (a.price || 0));
        console.table(rows.slice(0, limit));
        console.log(`Total cache entries: ${rows.length}`);
        return rows;
    };

    // Debug: games with NO captured steamPrice (only aksPrice, no real Steam cap).
    unsafeWindow.__wishlistMinPriceMissingSteam = function () {
        const rows = Object.entries(store)
            .filter(([, v]) => typeof v.steamPrice !== "number")
            .map(([appid, v]) => ({
                appid,
                aksPrice: typeof v.aksPrice === "number" ? v.aksPrice : null,
                price: typeof v.price === "number" ? v.price : null,
            }));
        console.table(rows);
        console.log(
            `Games without a captured steamPrice: ${rows.length} of ${Object.keys(store).length}`,
        );
        return rows;
    };

    // Debug: cache entries NOT seen this session. In API mode the cache
    // reconciles itself, so this only matters for the DOM fallback.
    unsafeWindow.__wishlistMinPriceExtras = function () {
        const extras = Object.keys(store).filter((id) => !sessionSeenIds.has(id));
        console.log(
            `Cached but NOT seen this session: ${extras.length} of ${Object.keys(store).length} cached`,
        );
        console.table(
            extras.map((id) => ({
                appid: id,
                name: store[id].name || "(no name)",
                ...store[id],
            })),
        );
        return extras;
    };

    // Diagnostics: bar counts and full cache dump (also returned as array).
    unsafeWindow.__wishlistMinPriceDump = function () {
        const counts = computeTotals();
        const gameTotal =
            apiWishlistTotal !== null ? apiWishlistTotal : counts.storeSize;
        log(
            `BAR COUNTS → on sale: ${counts.onSaleCount}, without price: ${counts.noPriceCount}, on wishlist: ${gameTotal} (fresh: ${counts.freshCount}, min: ${formatPrice(counts.total)}, current: ${formatPrice(counts.currentTotal)}, original: ${formatPrice(counts.originalTotal)})`,
        );
        const rows = Object.entries(store).map(([appid, v]) => ({
            appid,
            name: v.name || "(no name)",
            steamPrice: typeof v.steamPrice === "number" ? v.steamPrice : null,
            steamOriginal:
                typeof v.steamOriginalPrice === "number" ? v.steamOriginalPrice : null,
            discount: typeof v.discountPercent === "number" ? v.discountPercent : null,
            noPrice: v.noPrice === true,
            aksPrice: typeof v.aksPrice === "number" ? v.aksPrice : null,
            price: typeof v.price === "number" ? v.price : null,
        }));
        console.table(rows);
        log(`dump: ${rows.length} cache entries (returned as array)`);
        return rows;
    };

    // Diagnostics: what the panels actually rendered this session — the
    // same ground truth AugmentedSteam counts its stats from.
    unsafeWindow.__wishlistMinPriceDom = function () {
        if (domSnapshot.size === 0) {
            log("dom: snapshot empty — reload the wishlist and let the sweep finish");
            return null;
        }
        let withTag = 0;
        let withBadge = 0;
        let withoutTag = 0;
        const diffs = [];
        domSnapshot.forEach((snap, appid) => {
            if (snap.tag !== null) withTag++;
            else withoutTag++;
            if (snap.badge !== null && snap.badge > 0) withBadge++;
            const cache = store[appid] || {};
            const label = `"${cache.name || appid}"`;
            if (snap.tag === null && typeof cache.steamPrice === "number") {
                diffs.push(
                    `PHANTOM PRICE? ${appid} ${label} — cache steamPrice=${cache.steamPrice} but panel never showed a price tag (seen ${snap.seen}x)`,
                );
            }
            if (
                snap.badge !== null &&
                snap.badge > 0 &&
                cache.discountPercent !== snap.badge
            ) {
                diffs.push(
                    `BADGE MISMATCH ${appid} ${label} — panel=-${snap.badge}% but cache discountPercent=${cache.discountPercent ?? "none"}`,
                );
            }
            if (
                snap.tag !== null &&
                (snap.badge === null || snap.badge === 0) &&
                typeof cache.discountPercent === "number" &&
                cache.discountPercent > 0
            ) {
                diffs.push(
                    `STALE SALE? ${appid} ${label} — cache discountPercent=${cache.discountPercent}% but panel showed no badge (seen ${snap.seen}x)`,
                );
            }
        });
        log(
            `DOM SUMMARY (panels seen: ${domSnapshot.size}) → with price tag: ${withTag}, with badge: ${withBadge}, without tag: ${withoutTag} ← compare with AugmentedSteam (36 / 15)`,
        );
        if (diffs.length === 0) {
            log("dom vs cache: no discrepancies");
        } else {
            log(`dom vs cache: ${diffs.length} discrepancies`);
            diffs.forEach((d) => log("DOM DIFF →", d));
        }
        const rows = Array.from(domSnapshot.entries()).map(([appid, s]) => ({
            appid,
            tag: s.tag,
            badge: s.badge,
            seen: s.seen,
        }));
        console.table(rows);
        return rows;
    };

    // Diagnostics: toggle per-panel capture spam. Calls log() only when on.
    unsafeWindow.__wishlistMinPriceVerbose = function (on = true) {
        verboseCapture = Boolean(on);
        log(`verbose capture ${verboseCapture ? "ON" : "OFF"}`);
    };

    // Diagnostics: which entries were priced by the API (authoritative) and
    // which came from the DOM/fallback (can be stale on a long-open tab).
    // A single "dom/fallback" entry whose price changes after a reload is
    // the game contaminating the totals.
    unsafeWindow.__wishlistMinPriceSource = function () {
        const rows = Object.entries(store).map(([appid, v]) => ({
            appid,
            name: v.name || "(no name)",
            source: typeof v.apiTs === "number" ? "api" : "dom/fallback",
            steamPrice: typeof v.steamPrice === "number" ? v.steamPrice : null,
            steamOriginal:
                typeof v.steamOriginalPrice === "number"
                    ? v.steamOriginalPrice
                    : null,
            discount:
                typeof v.discountPercent === "number" ? v.discountPercent : null,
            aksPrice: typeof v.aksPrice === "number" ? v.aksPrice : null,
            noPrice: v.noPrice === true,
        }));
        const nonApi = rows.filter((r) => r.source !== "api");
        log(
            `sources → api: ${rows.length - nonApi.length}, dom/fallback: ${nonApi.length}`,
        );
        console.table(nonApi);
        return nonApi;
    };

    // Diagnostics (manual): compares our cache against the legacy
    // wishlistdata endpoint (what the old wishlist — and likely
    // AugmentedSteam — historically used). Never runs on its own.
    unsafeWindow.__wishlistMinPriceCompare = async function () {
        const steamid = resolveSteamId();
        if (!steamid) {
            log("compare: could not resolve a steamid");
            return null;
        }
        log("compare: fetching wishlistdata for", steamid);
        const fetchPage = (page) =>
            new Promise((resolve) => {
                const suffix = page === 0 ? "" : `?p=${page}`;
                GM_xmlhttpRequest({
                    method: "GET",
                    timeout: STEAM_TIMEOUT_MS,
                    url:
                        `https://store.steampowered.com/wishlist/profiles/${steamid}` +
                        `/wishlistdata/${suffix}`,
                    onload: (res) => {
                        try {
                            resolve(JSON.parse(res.responseText));
                        } catch (e) {
                            log(`compare: page ${page} returned non-JSON`);
                            resolve(null);
                        }
                    },
                    onerror: () => {
                        log(`compare: page ${page} network error`);
                        resolve(null);
                    },
                    ontimeout: () => {
                        log(`compare: page ${page} timed out`);
                        resolve(null);
                    },
                });
            });
        const merged = {};
        for (let page = 0; page < 10; page++) {
            const data = await fetchPage(page);
            if (!data) break;
            const keys = Object.keys(data).filter((k) => /^\d+$/.test(k));
            log(`compare: page ${page} → ${keys.length} items`);
            if (keys.length === 0) break;
            keys.forEach((k) => {
                merged[k] = data[k];
            });
        }
        const appids = Object.keys(merged);
        if (appids.length === 0) {
            log("compare: got no appid-keyed data — raw sample:");
            console.log("[WMP] raw sample:", merged);
            return null;
        }
        log("compare: sample entry →", JSON.stringify(merged[appids[0]]));
        let wdSale = 0;
        let wdNoPrice = 0;
        const diffs = [];
        appids.forEach((appid) => {
            const wd = merged[appid] || {};
            const wdDiscount =
                typeof wd.discount_percent === "number" ? wd.discount_percent : null;
            const priceMap = wd.price && typeof wd.price === "object" ? wd.price : null;
            const hasPrice =
                wd.is_free_game === true ||
                (priceMap !== null && Object.keys(priceMap).length > 0);
            if (wdDiscount !== null && wdDiscount > 0) wdSale++;
            if (!hasPrice) wdNoPrice++;
            const cache = store[appid];
            const label = `"${(cache && cache.name) || wd.name || appid}"`;
            if (!cache) {
                diffs.push(`NOT IN CACHE ${appid} ${label}`);
                return;
            }
            const cacheSale = (cache.discountPercent ?? 0) > 0;
            if (((wdDiscount ?? 0) > 0) !== cacheSale) {
                diffs.push(
                    `SALE DIFF ${appid} ${label} — wishlistdata=${wdDiscount ?? "?"}% cache discountPercent=${cache.discountPercent ?? "none"}`,
                );
            }
            const cachePriced = typeof cache.steamPrice === "number";
            if (hasPrice !== cachePriced) {
                diffs.push(
                    `PRICE PRESENCE DIFF ${appid} ${label} — wishlistdata hasPrice=${hasPrice} cache steamPrice=${cachePriced ? cache.steamPrice : "none"}`,
                );
            }
        });
        log(
            `compare: wishlistdata counts → on sale: ${wdSale}, without price: ${wdNoPrice}, items: ${appids.length} ← if this is 36/15, this is the source AS uses`,
        );
        if (diffs.length === 0) log("compare: no differences vs cache");
        else {
            log(`compare: ${diffs.length} differences vs cache`);
            diffs.forEach((d) => log("COMPARE DIFF →", d));
        }
        return merged;
    };

    // ---------- Parseo / formato de precios ----------
    function extractCurrencySymbol(text) {
        if (!text) return null;
        const match = text.match(/[^\d,.\s-]+/);
        return match ? match[0].trim() : null;
    }

    function parsePrice(text) {
        if (!text) return null;

        const symbol = extractCurrencySymbol(text);
        if (symbol) currencySymbol = symbol;

        let cleaned = text.replace(/[^\d,.\-]/g, "").trim();
        if (!cleaned) return null;

        const lastComma = cleaned.lastIndexOf(",");
        const lastDot = cleaned.lastIndexOf(".");
        let decimalSep = null;

        if (lastComma > -1 && lastDot > -1) {
            decimalSep = lastComma > lastDot ? "," : ".";
        } else if (lastComma > -1) {
            decimalSep = ",";
        } else if (lastDot > -1) {
            decimalSep = ".";
        }

        if (decimalSep) {
            const thousandSep = decimalSep === "," ? "." : ",";
            cleaned = cleaned.split(thousandSep).join("");
            cleaned = cleaned.replace(decimalSep, ".");
        }

        const value = parseFloat(cleaned);
        return isNaN(value) ? null : value;
    }

    function formatPrice(value) {
        return (
            value
                .toLocaleString("de-DE", {
                    minimumFractionDigits: 2,
                    maximumFractionDigits: 2,
                })
                .replace(/\./g, " ") + currencySymbol
        );
    }

    // ---------- Per-game data extraction (DOM mode only) ----------
    function getAppIdFromLink(link) {
        const href = link.getAttribute("href") || link.href || "";
        const match = href.match(/\/app\/(\d+)/);
        return match ? match[1] : null;
    }

    function getLinkName(link) {
        return (
            link.textContent.trim() ||
            link.getAttribute("title")?.trim() ||
            link.getAttribute("aria-label")?.trim() ||
            ""
        );
    }

    function getPanelTitle(panel) {
        const titleContainer = panel.querySelector(".P-zVPa2bdmQ-");
        return titleContainer ? titleContainer.textContent.trim() : "";
    }

    function extractGameInfo(panel) {
        const appLinks = Array.from(panel.querySelectorAll('a[href*="/app/"]'));
        if (appLinks.length === 0) return null;

        const preferredLink = panel.querySelector('.P-zVPa2bdmQ- a[href*="/app/"]');
        const idLink = preferredLink || appLinks[0];
        const appid = getAppIdFromLink(idLink);
        if (!appid) return null;

        // Virtualization may update the href before painting the title;
        // only use names matching the appid to avoid mixing games.
        const nameLink = [preferredLink, ...appLinks].find(
            (link, index, links) =>
                link &&
                links.indexOf(link) === index &&
                getAppIdFromLink(link) === appid &&
                getLinkName(link),
        );

        return {
            appid,
            name: nameLink ? getLinkName(nameLink) : getPanelTitle(panel),
        };
    }

    // Price tag of a wishlist panel: on-sale games show the struck-through
    // original next to the discounted price ("11,79€ 10,02€"), the rest a
    // single value. Class names are hashed, so the primary path just parses
    // every element inside the known price-tag container (max = original,
    // min = discounted; duplicates from wrappers are harmless); the
    // fallback groups leaf nodes holding a currency amount by parent when
    // Valve renames those classes.
    function buildSteamPrices(values) {
        if (values.length === 0) return { original: null, discounted: null };
        if (values.length === 1) {
            return { original: values[0], discounted: values[0] };
        }
        return {
            original: Math.max(...values),
            discounted: Math.min(...values),
        };
    }

    function extractSteamPrices(panel) {
        const tag = panel.querySelector(".-OkCLv-56oQ-");
        if (tag) {
            const values = Array.from(tag.querySelectorAll("*"))
                .map((el) => parsePrice(el.textContent))
                .filter((v) => v !== null);
            if (values.length > 0) return buildSteamPrices(values);
        }

        // Fallback: leaf divs showing an amount, grouped by their parent,
        // so stray amounts elsewhere in the panel don't mix in.
        const groups = new Map();
        panel.querySelectorAll("div").forEach((el) => {
            if (el.children.length > 0) return;
            if (!el.textContent.includes(currencySymbol)) return;
            const value = parsePrice(el.textContent);
            if (value === null) return;
            const parent = el.parentElement;
            if (!groups.has(parent)) groups.set(parent, []);
            groups.get(parent).push(value);
        });
        for (const values of groups.values()) {
            if (values.length > 0) return buildSteamPrices(values);
        }
        return { original: null, discounted: null };
    }

    function extractDiscountPercent(panel) {
        // Sale badge text like "-66%" lives in its own leaf div near the
        // price tag. Search leaf nodes to avoid matching unrelated text.
        let found = null;
        panel.querySelectorAll("div, span").forEach((el) => {
            if (el.children.length > 0) return;
            const text = el.textContent.trim();
            const m = text.match(/^-\s*(\d+)\s*%$/);
            if (!m) return;
            const n = parseInt(m[1], 10);
            if (!isNaN(n) && n > 0 && n < 100) found = n;
        });
        return found;
    }

    // Loose name match so the API's "most relevant" result can't pass off
    // a different game's price (roman numerals, apostrophes, subtitles).
    const ROMAN_MAP = {
        i: "1",
        ii: "2",
        iii: "3",
        iv: "4",
        v: "5",
        vi: "6",
        vii: "7",
        viii: "8",
        ix: "9",
        x: "10",
        xi: "11",
        xii: "12",
        xiii: "13",
    };

    function normalizeTitle(s) {
        if (typeof s !== "string") return "";
        return s
            .toLowerCase()
            .replace(/['’]/g, "") // don't -> dont
            .replace(/[™®©]/g, "") // brand marks
            .replace(/[^a-z0-9]+/g, " ") // punctuation -> space
            .trim()
            .split(/\s+/)
            .filter(Boolean)
            .map((tok) => (ROMAN_MAP[tok] !== undefined ? ROMAN_MAP[tok] : tok))
            .join(" ");
    }

    function isNameMatch(a, b) {
        const na = normalizeTitle(a);
        const nb = normalizeTitle(b);
        if (!na || !nb) return false;
        if (na === nb) return true;

        const tokensA = na.split(" ").filter(Boolean);
        const tokensB = nb.split(" ").filter(Boolean);
        const [shorter, longer] =
            tokensA.length <= tokensB.length
                ? [tokensA, new Set(tokensB)]
                : [tokensB, new Set(tokensA)];

        if (shorter.length === 0) return false;
        const overlap = shorter.filter((tok) => longer.has(tok)).length;
        return overlap / shorter.length >= 0.7;
    }

    // Merge known data with the new prices and recompute the minimum.
    function updateGamePrice(
        appid,
        { steamPrice, steamOriginalPrice, discountPercent, aksPrice, name } = {},
    ) {
        const existing = store[appid] || {};
        const merged = { ...existing };
        let changed = false;

        if (steamPrice !== undefined) {
            changed = existing.steamPrice !== steamPrice || changed;
            merged.steamPrice = steamPrice;
        }
        if (steamOriginalPrice !== undefined) {
            changed =
                existing.steamOriginalPrice !== steamOriginalPrice || changed;
            merged.steamOriginalPrice = steamOriginalPrice;
        }
        if (discountPercent !== undefined) {
            changed = existing.discountPercent !== discountPercent || changed;
            merged.discountPercent = discountPercent;
        }
        if (aksPrice !== undefined) {
            changed = existing.aksPrice !== aksPrice || changed;
            merged.aksPrice = aksPrice;
        }
        if (name) {
            const cleanName = name.trim();
            changed = existing.name !== cleanName || changed;
            merged.name = cleanName;
        }

        const candidates = [merged.steamPrice, merged.aksPrice].filter(
            (v) => typeof v === "number",
        );
        if (candidates.length === 0) {
            store[appid] = merged;
            return changed;
        }

        const price = Math.min(...candidates);
        changed = existing.price !== price || changed;
        merged.price = price;
        merged.ts = Date.now();
        store[appid] = merged;
        return changed;
    }

    // ---------- Steam API ----------
    // steamLoginSecure is "<steamid>%7C%7C<jwt>" (the token is URL-encoded):
    // the id is the part before the first "%". NOTE: Steam sets this cookie
    // with HttpOnly, so document.cookie can't normally see it; kept as a
    // last resort in case Steam ever drops the flag.
    function getCookieSteamId() {
        const m = document.cookie.match(/(?:^|;\s*)steamLoginSecure=([^;]*)/);
        if (!m) return null;
        const value = m[1];
        const cut = value.indexOf("%");
        const id = cut > -1 ? value.slice(0, cut) : value.split("||")[0];
        return /^\d{17}$/.test(id) ? id : null;
    }

    // The wishlist app embeds the wishlist OWNER's steamid in its SSR state
    // (React Query key "wishlistcategories"); present even for private or
    // rate-limited wishlists, so it resolves /wishlist/id/<vanity> for your
    // own wishlist AND other people's.
    function getSsrOwnerSteamId() {
        try {
            const scripts = document.querySelectorAll("script");
            for (const s of scripts) {
                const m = s.textContent.match(/wishlistcategories[^0-9]{1,40}(\d{17})/);
                if (m) return m[1];
            }
        } catch (e) {
            /* ignore */
        }
        return null;
    }

    function resolveSteamId() {
        // /wishlist/profiles/<id> and /wishlist/<id>
        const m = location.pathname.match(/\/wishlist\/(?:profiles\/)?(\d{17})/);
        if (m) return m[1];
        // Owner from the page's SSR state: covers vanity URLs of any wishlist.
        const ssrId = getSsrOwnerSteamId();
        if (ssrId) return ssrId;
        // Logged-in user's own steamid.
        const config = unsafeWindow.UserConfig;
        if (
            config &&
            typeof config.steamid === "string" &&
            /^\d{17}$/.test(config.steamid)
        ) {
            return config.steamid;
        }
        const g = unsafeWindow.g_steamID;
        if (typeof g === "string" && /^\d{17}$/.test(g)) return g;
        const cookieId = getCookieSteamId();
        if (cookieId) return cookieId;
        return DEFAULT_STEAMID;
    }

    // ---------- Store country / language (dynamic, like AugmentedSteam) ----------
    function getStoreCountry() {
        try {
            const usp = new URLSearchParams(location.search);
            if (usp.has("cc")) {
                const cc = usp.get("cc");
                if (cc && /^[a-z]{2}$/i.test(cc)) return cc.toUpperCase();
            }
            const cfgEl = document.querySelector("#application_config, #webui_config");
            if (cfgEl && cfgEl.dataset.config) {
                const j = JSON.parse(cfgEl.dataset.config);
                if (j.COUNTRY && typeof j.COUNTRY === "string") return j.COUNTRY.toUpperCase();
            }
            if (unsafeWindow.Config && typeof unsafeWindow.Config.COUNTRY === "string") {
                return unsafeWindow.Config.COUNTRY.toUpperCase();
            }
            const m = document.documentElement.innerHTML.match(/GDynamicStore\.Init\(.+?,\s*'([A-Z]{2})'/);
            if (m) return m[1].toUpperCase();
            // AugmentedSteam also tries store_user_config via dataset, handled above
        } catch (e) {
            /* ignore */
        }
        return FALLBACK_CC.toUpperCase();
    }

    function getStoreLanguage() {
        try {
            const cfgEl = document.querySelector("#application_config, #webui_config");
            if (cfgEl && cfgEl.dataset.config) {
                const j = JSON.parse(cfgEl.dataset.config);
                if (j.LANGUAGE && typeof j.LANGUAGE === "string") return j.LANGUAGE.toLowerCase();
            }
            if (unsafeWindow.Config && typeof unsafeWindow.Config.LANGUAGE === "string") {
                return unsafeWindow.Config.LANGUAGE.toLowerCase();
            }
            const m = document.documentElement.innerHTML.match(/g_strLanguage\s*=\s*["']([^"']+)["']/);
            if (m) return m[1].toLowerCase();
        } catch (e) {
            /* ignore */
        }
        return FALLBACK_LANG.toLowerCase(); // "spanish" for ES fallback
    }

    // For appdetails (expects cc=es & l=es or l=spanish). Map full name to 2-letter when needed.
    const LANG_TO_CC = {
        english: "en",
        spanish: "es",
        french: "fr",
        german: "de",
        italian: "it",
        portuguese: "pt",
        brazilian: "pt-br",
        russian: "ru",
        polish: "pl",
        dutch: "nl",
        swedish: "sv",
        norwegian: "no",
        danish: "da",
        finnish: "fi",
        czech: "cs",
        hungarian: "hu",
        greek: "el",
        turkish: "tr",
        japanese: "ja",
        korean: "ko",
        schinese: "zh-cn",
        tchinese: "zh-tw",
        thai: "th",
        ukrainian: "uk",
    };
    function languageToShort(lang) {
        if (!lang) return FALLBACK_CC;
        const low = lang.toLowerCase();
        if (/^[a-z]{2}(-[a-z]{2})?$/.test(low)) return low; // already short
        return LANG_TO_CC[low] || low.slice(0, 2);
    }

    // ---------- IStoreBrowseService (manual protobuf) ----------
    // Manual varint / length-delimited codec to avoid pulling protobufjs.
    // Request: CStoreBrowse_GetItems_Request { ids(1):StoreItemID, context(2), dataRequest(3) }
    // Response: CStoreBrowse_GetItems_Response { storeItems(1):StoreItem }
    // Only the subset we need is implemented.
    function encodeVarint(value) {
        let n = typeof value === "bigint" ? value : BigInt(value >>> 0);
        // For signed negative we use BigInt directly; callers pass unsigned.
        if (typeof value === "bigint") n = value;
        else if (value < 0) n = BigInt(value);
        const out = [];
        while (n > 0x7fn) {
            out.push(Number((n & 0x7fn) | 0x80n));
            n >>= 7n;
        }
        out.push(Number(n & 0x7fn));
        return out;
    }
    function encodeTag(field, wire) {
        return encodeVarint((field << 3) | wire);
    }
    function encodeStringField(fieldNum, str) {
        const utf8 = new TextEncoder().encode(str);
        return [...encodeTag(fieldNum, 2), ...encodeVarint(utf8.length), ...utf8];
    }
    function encodeVarintField(fieldNum, value) {
        return [...encodeTag(fieldNum, 0), ...encodeVarint(value)];
    }
    function encodeMessageField(fieldNum, innerBytes) {
        return [...encodeTag(fieldNum, 2), ...encodeVarint(innerBytes.length), ...innerBytes];
    }
    function buildGetItemsPayload(appids, countryCode, language) {
        const out = [];
        // ids: repeated StoreItemID (field 1)
        for (const a of appids) {
            const appidNum = Number(a) >>> 0;
            const inner = encodeVarintField(1, appidNum); // StoreItemID.appid = 1
            out.push(...encodeMessageField(1, inner));
        }
        // context (field 2): StoreBrowseContext
        const ctxInner = [];
        if (language) ctxInner.push(...encodeStringField(1, language));
        // elanguage (field 2) is optional int32; we omit to let server derive from language string
        if (countryCode) ctxInner.push(...encodeStringField(3, countryCode));
        ctxInner.push(...encodeVarintField(4, 1)); // steamRealm = 1 (k_ESteamRealmGlobal)
        out.push(...encodeMessageField(2, ctxInner));
        // dataRequest (field 3): StoreBrowseItemDataRequest
        // AugmentedSteam uses includeBasicInfo:true alone for wishlist totals.
        // includeBasicInfo is field 10 bool (tag 80 => 0x50)
        const drInner = encodeVarintField(10, 1);
        out.push(...encodeMessageField(3, drInner));
        return new Uint8Array(out);
    }
    function base64EncodeBytes(bytes) {
        let binary = "";
        const chunk = 8192;
        for (let i = 0; i < bytes.length; i += chunk) {
            const slice = bytes.subarray(i, Math.min(i + chunk, bytes.length));
            binary += String.fromCharCode.apply(null, slice);
        }
        return btoa(binary);
    }
    // --- Decoder helpers (varint/length-delimited) ---
    function readVarint(buf, pos) {
        let result = 0n;
        let shift = 0n;
        let i = pos;
        let b;
        do {
            if (i >= buf.length) throw new Error("varint overflow");
            b = BigInt(buf[i++]);
            result |= (b & 0x7fn) << shift;
            shift += 7n;
        } while ((b & 0x80n) !== 0n);
        // Return as Number when safe, otherwise BigInt
        const value = result <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(result) : result;
        return { value, bytesRead: i - pos };
    }
    function readString(buf, pos, len) {
        const slice = buf.subarray(pos, pos + len);
        return new TextDecoder().decode(slice);
    }
    function skipField(buf, pos, wire) {
        if (wire === 0) {
            const r = readVarint(buf, pos);
            return pos + r.bytesRead;
        }
        if (wire === 1) return pos + 8;
        if (wire === 2) {
            const r = readVarint(buf, pos);
            return pos + r.bytesRead + Number(r.value);
        }
        if (wire === 5) return pos + 4;
        throw new Error("unsupported wire " + wire);
    }
    function decodePurchaseOption(buf) {
        let pos = 0;
        const o = {};
        while (pos < buf.length) {
            const tag = readVarint(buf, pos);
            pos += tag.bytesRead;
            const field = Number(tag.value) >> 3;
            const wire = Number(tag.value) & 7;
            if (wire === 2) {
                const len = readVarint(buf, pos);
                pos += len.bytesRead;
                const str = readString(buf, pos, Number(len.value));
                pos += Number(len.value);
                if (field === 8) o.formattedFinalPrice = str;
                else if (field === 9) o.formattedOriginalPrice = str;
                else if (field === 15) o.formattedPriceBeforeBundleDiscount = str;
            } else if (wire === 0) {
                const v = readVarint(buf, pos);
                pos += v.bytesRead;
                const val = typeof v.value === "bigint" ? Number(v.value) : v.value;
                if (field === 1) o.packageid = val;
                else if (field === 2) o.bundleid = val;
                else if (field === 5) o.finalPriceInCents = typeof v.value === "bigint" ? v.value : BigInt(val);
                else if (field === 6) o.originalPriceInCents = typeof v.value === "bigint" ? v.value : BigInt(val);
                else if (field === 10) o.discountPct = val;
                else if (field === 12) o.bundleDiscountPct = val;
                else if (field === 14) o.priceBeforeBundleDiscount = typeof v.value === "bigint" ? v.value : BigInt(val);
                else if (field === 44) o.lowestRecentPriceInCents = typeof v.value === "bigint" ? v.value : BigInt(val);
            } else if (wire === 1) pos += 8;
            else if (wire === 5) pos += 4;
            else throw new Error("unsupported wire in purchaseOption " + wire);
        }
        return o;
    }
    function decodeStoreItem(buf) {
        let pos = 0;
        const item = { name: "", purchaseOption: null };
        while (pos < buf.length) {
            const tag = readVarint(buf, pos);
            pos += tag.bytesRead;
            const field = Number(tag.value) >> 3;
            const wire = Number(tag.value) & 7;
            if (wire === 0) {
                const v = readVarint(buf, pos);
                pos += v.bytesRead;
                const val = typeof v.value === "bigint" ? Number(v.value) : v.value;
                if (field === 1) item.itemType = val;
                else if (field === 2) item.id = val;
                else if (field === 3) item.success = val;
                else if (field === 4) item.visible = !!val;
                else if (field === 9) item.appid = val;   // StoreItem.appid is field 9 (tag 72)
                else if (field === 13) item.isFree = !!val; // StoreItem.isFree is field 13 (tag 104)
                else if (field === 14) item.isEarlyAccess = !!val;
                else if (field === 55) item.unlisted = !!val; // tag 440
                // else ignore
            } else if (wire === 2) {
                const len = readVarint(buf, pos);
                pos += len.bytesRead;
                const nlen = Number(len.value);
                const slice = buf.subarray(pos, pos + nlen);
                pos += nlen;
                if (field === 6) item.name = readString(slice, 0, slice.length);
                else if (field === 7) item.storeUrlPath = readString(slice, 0, slice.length);
                else if (field === 40) item.bestPurchaseOption = decodePurchaseOption(slice);
                else if (field === 41) { /* purchaseOptions repeated - ignore for now */ }
                // else skip (tags, assets etc)
            } else if (wire === 1) {
                pos += 8;
            } else if (wire === 5) {
                pos += 4;
            } else {
                throw new Error("unknown wire " + wire);
            }
        }
        // Normalize id/appid (response usually carries id; appid when requested by appid)
        if (item.appid == null && item.id != null) item.appid = item.id;
        if (item.id == null && item.appid != null) item.id = item.appid;
        return item;
    }
    function decodeGetItemsResponse(buf) {
        let pos = 0;
        const out = [];
        while (pos < buf.length) {
            const tag = readVarint(buf, pos);
            pos += tag.bytesRead;
            const field = Number(tag.value) >> 3;
            const wire = Number(tag.value) & 7;
            if (field === 1 && wire === 2) {
                const len = readVarint(buf, pos);
                pos += len.bytesRead;
                const nlen = Number(len.value);
                const slice = buf.subarray(pos, pos + nlen);
                pos += nlen;
                out.push(decodeStoreItem(slice));
            } else {
                // unknown field -> skip payload
                if (wire === 0) {
                    const v = readVarint(buf, pos);
                    pos += v.bytesRead;
                } else if (wire === 1) pos += 8;
                else if (wire === 2) {
                    const len = readVarint(buf, pos);
                    pos += len.bytesRead;
                    pos += Number(len.value);
                } else if (wire === 5) pos += 4;
                else throw new Error("unknown wire in response " + wire);
            }
        }
        return out;
    }

    // ---------- Web API token (for IStoreBrowseService) ----------
    let cachedWebApiToken = null;
    let cachedWebApiTokenAt = 0;
    let tokenFetchPromise = null;
    // Steam web-api tokens expire; a stale cache makes StoreBrowse 401 after
    // the tab has been open for a while. TTL keeps the cache short-lived.
    const TOKEN_TTL_MS = 10 * 60 * 1000; // 10 min
    function extractTokenFromDom() {
        try {
            const el = document.querySelector("#application_config");
            if (el) {
                if (el.dataset.store_user_config) {
                    const j = JSON.parse(el.dataset.store_user_config);
                    if (j.webapi_token) return j.webapi_token;
                    if (j.webapiToken) return j.webapiToken;
                }
                if (el.dataset.config) {
                    const j = JSON.parse(el.dataset.config);
                    if (j.WEBAPI_TOKEN) return j.WEBAPI_TOKEN;
                }
            }
            const el2 = document.querySelector("#webui_config");
            if (el2 && el2.dataset.config) {
                const j = JSON.parse(el2.dataset.config);
                if (j.WEBAPI_TOKEN) return j.WEBAPI_TOKEN;
            }
            if (unsafeWindow.Config && unsafeWindow.Config.WEBAPI_TOKEN) return unsafeWindow.Config.WEBAPI_TOKEN;
            // SSR.loaderData like AugmentedSteam: SSR.loaderData entries contain strWebAPIToken
            const tryGlobal = (key) => {
                try {
                    const v = unsafeWindow[key];
                    if (Array.isArray(v)) {
                        for (const e of v) {
                            const s = typeof e === "string" ? JSON.parse(e) : e;
                            if (s && s.strWebAPIToken) return s.strWebAPIToken;
                            if (s && s.webapi_token) return s.webapi_token;
                        }
                    } else if (v && typeof v === "object" && v.strWebAPIToken) return v.strWebAPIToken;
                } catch (e) { /* ignore */ }
                return null;
            };
            // Check known globals via unsafeWindow
            const candidates = ["SSR", "SSR.loaderData", "Config", "UserConfig"];
            for (const c of candidates) {
                const parts = c.split(".");
                let cur = unsafeWindow;
                for (const p of parts) cur = cur && cur[p];
                if (!cur) continue;
                if (Array.isArray(cur)) {
                    for (const e of cur) {
                        try {
                            const o = typeof e === "string" ? JSON.parse(e) : e;
                            if (o && o.strWebAPIToken) return o.strWebAPIToken;
                        } catch (e2) { /* ignore */ }
                    }
                } else if (typeof cur === "object" && cur.strWebAPIToken) return cur.strWebAPIToken;
            }
            // Also check scripts for strWebAPIToken
            const scripts = document.querySelectorAll("script");
            for (const s of scripts) {
                const txt = s.textContent;
                if (!txt || !txt.includes("strWebAPIToken")) continue;
                const m = txt.match(/strWebAPIToken["']\s*:\s*["']([^"']+)["']/);
                if (m) return m[1];
                const m2 = txt.match(/webapi_token["']\s*:\s*["']([^"']+)["']/);
                if (m2) return m2[1];
            }
        } catch (e) {
            /* ignore */
        }
        return null;
    }
    async function getWebApiToken() {
        // Steam web-api tokens expire: a tab open for hours can keep a dead
        // token cached, silently making StoreBrowse fail (401) on refresh.
        if (cachedWebApiToken && Date.now() - (cachedWebApiTokenAt || 0) < TOKEN_TTL_MS) {
            return cachedWebApiToken;
        }
        const domTok = extractTokenFromDom();
        if (domTok) {
            cachedWebApiToken = domTok;
            cachedWebApiTokenAt = Date.now();
            return cachedWebApiToken;
        }
        if (tokenFetchPromise) return tokenFetchPromise;
        tokenFetchPromise = new Promise((resolve) => {
            GM_xmlhttpRequest({
                method: "GET",
                url: `${location.origin}/pointssummary/ajaxgetasyncconfig`,
                timeout: STEAM_TIMEOUT_MS,
                headers: { Accept: "application/json" },
                onload: function (res) {
                    try {
                        const j = JSON.parse(res.responseText);
                        const tok = j && j.data && (j.data.webapi_token || j.data.webapiToken);
                        if (tok) {
                            cachedWebApiToken = tok;
                            cachedWebApiTokenAt = Date.now();
                            log("webapi_token acquired via ajaxgetasyncconfig");
                        } else log("ajaxgetasyncconfig: no token in response");
                    } catch (e) { log("ajaxgetasyncconfig parse failed", e); }
                    resolve(cachedWebApiToken || null);
                },
                onerror: function () { log("ajaxgetasyncconfig network error"); resolve(null); },
                ontimeout: function () { log("ajaxgetasyncconfig timeout"); resolve(null); },
            });
        });
        const t = await tokenFetchPromise;
        tokenFetchPromise = null;
        return t;
    }

    // ---------- IStoreBrowseService fetch ----------
    function browseFetchChunk(appids) {
        return new Promise(async (resolve) => {
            const token = await getWebApiToken();
            if (!token) {
                resolve({ ok: false, error: "no_token" });
                return;
            }
            const country = getStoreCountry(); // e.g. "ES"
            const language = getStoreLanguage(); // e.g. "spanish"
            const payload = buildGetItemsPayload(appids, country, language);
            const b64 = base64EncodeBytes(payload);
            const url =
                "https://api.steampowered.com/IStoreBrowseService/GetItems/v1" +
                `?access_token=${encodeURIComponent(token)}` +
                `&input_protobuf_encoded=${encodeURIComponent(b64)}` +
                `&origin=${encodeURIComponent("https://store.steampowered.com")}`;
            log(`StoreBrowse request ${appids.length} ids → ${country}/${language} (payload ${payload.length}B)`);
            GM_xmlhttpRequest({
                method: "GET",
                url,
                timeout: STEAM_TIMEOUT_MS,
                responseType: "arraybuffer",
                headers: { Accept: "application/octet-stream" },
                onload: function (res) {
                    if (res.status < 200 || res.status >= 300) {
                        log(`StoreBrowse HTTP ${res.status} for ${appids.length} ids`);
                        resolve({ ok: false, error: "http_" + res.status });
                        return;
                    }
                    try {
                        const buf = res.response instanceof ArrayBuffer
                            ? new Uint8Array(res.response)
                            : new Uint8Array(res.response || []);
                        // Some GM implementations return response as string for arraybuffer - fallback
                        if (buf.length === 0 && res.responseText) {
                            // try base64? but assume empty means error
                            resolve({ ok: false, error: "empty" });
                            return;
                        }
                        const items = decodeGetItemsResponse(buf);
                        resolve({ ok: true, items });
                    } catch (e) {
                        console.warn("[WishlistMinPrice] StoreBrowse decode failed", e);
                        resolve({ ok: false, error: "decode" });
                    }
                },
                onerror: function (e) { log("StoreBrowse network error", e); resolve({ ok: false, error: "network" }); },
                ontimeout: function () { log("StoreBrowse timeout"); resolve({ ok: false, error: "timeout" }); },
            });
        });
    }

    async function fetchStoreBrowsePrices(appids) {
        const batchCount = Math.ceil(appids.length / STORE_BROWSE_BATCH_SIZE);
        const totals = { priced: 0, noPrice: 0, failed: 0, visibleHidden: 0 };
        const allFailedIds = [];
        let batchIndex = 0;
        let anySuccess = false;
        for (let i = 0; i < appids.length; i += STORE_BROWSE_BATCH_SIZE) {
            const chunk = appids.slice(i, i + STORE_BROWSE_BATCH_SIZE);
            batchIndex++;
            const res = await browseFetchChunk(chunk);
            let changed = false;
            if (res.ok && Array.isArray(res.items)) {
                anySuccess = true;
                // Freshness marker: entries priced by the API become
                // authoritative; DOM capture must not overwrite them (panels
                // on a long-open tab can be stale or mid-swap).
                const now = Date.now();
                const stamp = (appid) => {
                    if (store[appid]) store[appid].apiTs = now;
                };
                const pricedIds = [];
                const noPriceIds = [];
                const hiddenIds = [];
                const failedIds = [];
                // Map by appid string for quick lookup; StoreItem.id may be number
                const map = new Map();
                for (const it of res.items) {
                    const key = String(it.appid ?? it.id ?? "");
                    if (key) map.set(key, it);
                }
                for (const appid of chunk) {
                    const it = map.get(String(appid));
                    if (!it) { failedIds.push(appid); continue; }
                    if (it.success !== 1) {
                        // StoreItem not found / unavailable
                        failedIds.push(appid);
                        continue;
                    }
                    const name = it.name;
                    if (name) {
                        if ((store[appid] || {}).name !== name) {
                            store[appid] = { ...(store[appid] || {}), name };
                            changed = true;
                        }
                        if ((store[appid] || {}).is_free !== !!it.isFree) {
                            store[appid] = { ...(store[appid] || {}), is_free: !!it.isFree };
                            changed = true;
                        }
                    }
                    if (it.isFree) {
                        // Free game: treat as priced 0 but counts as noPrice for stats (like AugmentedSteam)
                        // We keep steamPrice 0 so original/current don't inflate, but stats counts as without price.
                        if (typeof (store[appid] || {}).steamPrice !== "number") {
                            changed = updateGamePrice(appid, { steamPrice: 0, steamOriginalPrice: 0, discountPercent: 0, name }) || changed;
                        }
                        stamp(appid);
                        noPriceIds.push(appid);
                        continue;
                    }
                    const po = it.bestPurchaseOption;
                    if (po && (po.finalPriceInCents != null)) {
                        // Convert cents -> EUR. finalPriceInCents is int64 cents
                        const cents = typeof po.finalPriceInCents === "bigint" ? po.finalPriceInCents : BigInt(po.finalPriceInCents);
                        const final = Number(cents) / 100;
                        const origCents = po.originalPriceInCents != null ? (typeof po.originalPriceInCents === "bigint" ? po.originalPriceInCents : BigInt(po.originalPriceInCents)) : cents;
                        const original = Number(origCents) / 100;
                        const discount = typeof po.discountPct === "number" ? po.discountPct : 0;
                        // Detect currency symbol from formatted price if present
                        if (po.formattedFinalPrice) {
                            const sym = extractCurrencySymbol(po.formattedFinalPrice);
                            if (sym) currencySymbol = sym;
                        }
                        // A price appeared: drop noPrice sentinel
                        if ((store[appid] || {}).noPrice === true) {
                            delete store[appid].noPrice;
                            changed = true;
                        }
                        pricedIds.push(appid);
                        changed = updateGamePrice(appid, { steamPrice: final, steamOriginalPrice: original, discountPercent: discount, name }) || changed;
                        stamp(appid);
                        continue;
                    }
                    // No purchase option -> without price
                    // If visible=false but no price, AugmentedSteam counts as hidden (k)
                    if (it.visible === false) hiddenIds.push(appid);
                    else noPriceIds.push(appid);
                    const entry = store[appid] || {};
                    const clean = { ...entry, noPrice: true };
                    if (name && !clean.name) clean.name = name;
                    const hadPrice = clean.steamPrice !== undefined || clean.steamOriginalPrice !== undefined || clean.discountPercent !== undefined || clean.price !== undefined || clean.ts !== undefined;
                    delete clean.steamPrice; delete clean.steamOriginalPrice; delete clean.discountPercent; delete clean.price; delete clean.ts;
                    if (hadPrice || entry.noPrice !== true) {
                        store[appid] = clean;
                        changed = true;
                    }
                    stamp(appid);
                }
                totals.priced += pricedIds.length;
                totals.noPrice += noPriceIds.length;
                totals.visibleHidden += hiddenIds.length;
                totals.failed += failedIds.length;
                allFailedIds.push(...failedIds);
                log(`StoreBrowse batch ${batchIndex}/${batchCount} → priced:${pricedIds.length} noPrice:${noPriceIds.length} hidden:${hiddenIds.length} failed:${failedIds.length}${failedIds.length ? " " + failedIds.join(",") : ""}`);
            } else {
                log(`StoreBrowse batch ${batchIndex}/${batchCount} → request failed (${res.error})`);
                totals.failed += chunk.length;
                // Early break on fatal token error? Continue to try other chunks anyway
                if (res.error === "no_token" || String(res.error).startsWith("http_401") || String(res.error).startsWith("http_403")) {
                    allFailedIds.push(...chunk);
                    break;
                }
            }
            if (changed) persistStore();
            inject();
        }
        log(`StoreBrowse totals → priced:${totals.priced} noPrice:${totals.noPrice} hidden:${totals.visibleHidden} failed:${totals.failed} (chunks ${batchCount})`);
        return { ok: anySuccess, failed: allFailedIds };
    }

    // GM_xmlhttpRequest wrapper with timeout and retries; always resolves
    // {ok, json?, error?}, never throws.
    function steamFetch(url, { retries = 1 } = {}) {
        return new Promise((resolve) => {
            const attempt = (remaining) => {
                GM_xmlhttpRequest({
                    method: "GET",
                    url,
                    timeout: STEAM_TIMEOUT_MS,
                    headers: { Accept: "application/json" },
                    onload: function (res) {
                        let json = null;
                        try {
                            json = JSON.parse(res.responseText);
                        } catch (e) {
                            console.warn(
                                "[WishlistMinPrice] Non-JSON response from Steam:",
                                url,
                            );
                        }
                        if (json !== null) {
                            resolve({ ok: true, json });
                        } else if (remaining > 0) {
                            setTimeout(() => attempt(remaining - 1), STEAM_RETRY_DELAY_MS);
                        } else {
                            resolve({ ok: false, error: "invalid-json" });
                        }
                    },
                    onerror: function (err) {
                        console.warn(
                            "[WishlistMinPrice] Network error with Steam:",
                            url,
                            err,
                        );
                        if (remaining > 0) {
                            setTimeout(() => attempt(remaining - 1), STEAM_RETRY_DELAY_MS);
                        } else {
                            resolve({ ok: false, error: "network" });
                        }
                    },
                    ontimeout: function () {
                        console.warn("[WishlistMinPrice] Steam timeout:", url);
                        if (remaining > 0) {
                            setTimeout(() => attempt(remaining - 1), STEAM_RETRY_DELAY_MS);
                        } else {
                            resolve({ ok: false, error: "timeout" });
                        }
                    },
                });
            };
            attempt(retries);
        });
    }

    async function fetchWishlist(steamid) {
        const url = `${WISHLIST_API_URL}?steamid=${steamid}`;
        const res = await steamFetch(url, { retries: 2 });
        if (!res.ok) return null;
        const items = res.json && res.json.response && res.json.response.items;
        return Array.isArray(items) ? items : null;
    }

    // Drop games that are no longer on the wishlist from the cache.
    function reconcileCache(appids) {
        const wanted = new Set(appids);
        let changed = false;
        Object.keys(store).forEach((id) => {
            if (!wanted.has(id)) {
                delete store[id];
                changed = true;
            }
        });
        if (changed) persistStore();
    }

    // Prices for all games in a few calls (filters=price_overview). Free or
    // region-unavailable games return "data":[] (no price_overview); unknown
    // appids come back with success:false and keep their price.
    async function fetchPricesBatch(appids) {
        const cc = getStoreCountry().toLowerCase();
        const langFull = getStoreLanguage();
        const langShort = languageToShort(langFull);
        const batchCount = Math.ceil(appids.length / PRICE_BATCH_SIZE);
        const totals = { priced: 0, noPrice: 0, failed: 0 };
        let batchIndex = 0;
        for (let i = 0; i < appids.length; i += PRICE_BATCH_SIZE) {
            const chunk = appids.slice(i, i + PRICE_BATCH_SIZE);
            batchIndex++;
            const url =
                `${APPDETAILS_URL}?appids=${chunk.join(",")}&cc=${cc}` +
                `&l=${langShort}&filters=price_overview`;
            const res = await steamFetch(url, { retries: 1 });
            let changed = false;

            if (res.ok && res.json) {
                // API-priced entries become authoritative (see fetchStoreBrowsePrices).
                const now = Date.now();
                const stamp = (appid) => {
                    if (store[appid]) store[appid].apiTs = now;
                };
                const pricedIds = [];
                const noPriceIds = [];
                const failedIds = [];
                chunk.forEach((appid) => {
                    const info = res.json[appid];
                    if (!info || info.success !== true) {
                        failedIds.push(appid);
                        return;
                    }

                    const d = info.data;
                    const p = d && !Array.isArray(d) ? d.price_overview : null;
                    if (p && typeof p.final === "number") {
                        const final = p.final / 100;
                        // A price appeared (e.g. a pre-order went live):
                        // drop the "without price" sentinel.
                        if ((store[appid] || {}).noPrice === true) {
                            delete store[appid].noPrice;
                            changed = true;
                        }
                        pricedIds.push(appid);
                        changed =
                            updateGamePrice(appid, {
                                steamPrice: final,
                                // Pre-discount price for the "original value"
                                // total; without a discount they're equal.
                                steamOriginalPrice:
                                    typeof p.initial === "number"
                                        ? p.initial / 100
                                        : final,
                                // Authoritative "on sale" flag; a bundle deal
                                // in the panel must not count as one.
                                discountPercent:
                                    typeof p.discount_percent === "number"
                                        ? p.discount_percent
                                        : 0,
                            }) || changed;
                        stamp(appid);
                        return;
                    }
                    // No price_overview (free, subscription, unreleased,
                    // unavailable): free games resolve to 0 via basic. The
                    // rest are marked "without price" and any cached price
                    // is purged — with no API price to overwrite it, a
                    // phantom DOM capture (panel read mid-swap) would
                    // otherwise survive forever.
                    const entry = store[appid] || {};
                    if (entry.is_free === true) {
                        noPriceIds.push(appid);
                        if (typeof entry.steamPrice !== "number") {
                            changed =
                                updateGamePrice(appid, {
                                    steamPrice: 0,
                                    steamOriginalPrice: 0,
                                    discountPercent: 0,
                                }) || changed;
                        }
                        stamp(appid);
                    } else {
                        if (typeof entry.is_free !== "boolean") {
                            queueNameFetch(appid);
                        }
                        noPriceIds.push(appid);
                        const clean = { ...entry, noPrice: true };
                        const hadPrice =
                            clean.steamPrice !== undefined ||
                            clean.steamOriginalPrice !== undefined ||
                            clean.discountPercent !== undefined ||
                            clean.price !== undefined ||
                            clean.ts !== undefined;
                        delete clean.steamPrice;
                        delete clean.steamOriginalPrice;
                        delete clean.discountPercent;
                        delete clean.price;
                        delete clean.ts;
                        if (hadPrice || entry.noPrice !== true) {
                            store[appid] = clean;
                            changed = true;
                        }
                        stamp(appid);
                    }
                });
                totals.priced += pricedIds.length;
                totals.noPrice += noPriceIds.length;
                totals.failed += failedIds.length;
                log(
                    `prices batch ${batchIndex}/${batchCount} → priced: ${pricedIds.length}, noPrice(data:[]): ${noPriceIds.length}${noPriceIds.length ? " " + noPriceIds.join(",") : ""}, success:false: ${failedIds.length}${failedIds.length ? " " + failedIds.join(",") : ""}`,
                );
            } else {
                log(`prices batch ${batchIndex}/${batchCount} → request failed (${res.error})`);
                totals.failed += chunk.length;
            }

            if (changed) persistStore();
            inject();
        }
        log(
            `API price totals → priced: ${totals.priced}, noPrice: ${totals.noPrice}, success:false: ${totals.failed} (total chunks ${batchCount})`,
        );
    }

    // Name (+ is_free) of a game: one basic call per appid (filters=basic
    // returns null with multiple appids).
    function queueNameFetch(appid) {
        if (pendingNameFetch.has(appid)) return;
        pendingNameFetch.add(appid);
        nameQueue.push(appid);
        processNameQueue();
    }

    function processNameQueue() {
        while (nameQueueActive < NAME_FETCH_CONCURRENCY && nameQueue.length > 0) {
            const appid = nameQueue.shift();
            nameQueueActive++;
            fetchName(appid).finally(() => {
                nameQueueActive--;
                processNameQueue();
            });
        }
    }

    async function fetchName(appid) {
        const cc = getStoreCountry().toLowerCase();
        const langFull = getStoreLanguage();
        const langShort = languageToShort(langFull);
        const url =
            `${APPDETAILS_URL}?appids=${appid}&cc=${cc}&l=${langShort}` +
            `&filters=basic`;
        const res = await steamFetch(url, { retries: 1 });
        let changed = false;

        const info = res.ok && res.json ? res.json[appid] : null;
        const data = info && info.success === true ? info.data : null;

        if (data && typeof data.name === "string" && data.name) {
            changed = updateGamePrice(appid, { name: data.name }) || changed;

            const isFree = data.is_free === true;
            if ((store[appid] || {}).is_free !== isFree) {
                store[appid] = { ...(store[appid] || {}), is_free: isFree };
                changed = true;
            }
            if (isFree && typeof store[appid].steamPrice !== "number") {
                changed =
                    updateGamePrice(appid, {
                        steamPrice: 0,
                        steamOriginalPrice: 0,
                    }) || changed;
            }
        } else {
            console.warn("[WishlistMinPrice] No Steam basic data for", appid);
        }

        pendingNameFetch.delete(appid);
        if (changed) {
            persistStore();
            queueAksForStale();
            inject();
        }
    }

    async function refreshFromApi(steamid) {
        // Panels on a long-open tab are stale (rendered at page load). While
        // the API pass runs, DOM capture must not write prices — after a
        // reset there is no apiTs protection yet and the observer would fill
        // entries with stale panel values that stick for API-missed games.
        domCaptureSuppressed = true;
        const items = await fetchWishlist(steamid);
        if (!items) {
            console.warn(
                "[WishlistMinPrice] Could not read the wishlist via the API " +
                "(private wishlist or timeout?), falling back to DOM mode",
            );
            domCaptureSuppressed = false;
            startDomMode();
            tryInject();
            return;
        }

        apiMode = true;
        const appids = items.map((i) => String(i.appid));
        apiWishlistTotal = appids.length;
        log(`wishlist API ok: ${appids.length} games`);

        reconcileCache(appids);

        // New games (no known name yet): one basic call each.
        appids.forEach((appid) => {
            if (!store[appid] || !store[appid].name) queueNameFetch(appid);
        });

        queueAksForStale();
        inject();

        // Prefer IStoreBrowseService (like AugmentedSteam, no scroll, correct bundle pricing).
        // Fallback to appdetails if token missing or request fails.
        let browseOk = false;
        let browseFailed = [];
        try {
            const browseRes = await fetchStoreBrowsePrices(appids);
            browseOk = browseRes.ok;
            browseFailed = browseRes.failed;
        } catch (e) {
            log("StoreBrowse exception, falling back to appdetails", e);
        }
        if (!browseOk) {
            log("StoreBrowse failed or no token — falling back to appdetails");
            await fetchPricesBatch(appids);
        } else if (browseFailed.length > 0) {
            // Second authoritative pass for the few items StoreBrowse could
            // not price (success != 1, not in response): appdetails is fresh
            // server data, whereas the visible panels can be hours old.
            log(`appdetails second pass for ${browseFailed.length} StoreBrowse misses: ${browseFailed.join(",")}`);
            await fetchPricesBatch(browseFailed);
        }
        domCaptureSuppressed = false;
        // Passive DOM capture only (no auto-scroll). MutationObserver already keeps panels in sync.
        scanVisiblePanels();
        inject();
    }

    // Queue AllKeyShop lookups for games whose AKS price is stale (or never
    // fetched). API mode only; DOM mode handles it in scanVisiblePanels.
    function queueAksForStale() {
        Object.entries(store).forEach(([appid, entry]) => {
            const name =
                entry && typeof entry.name === "string" ? entry.name.trim() : "";
            if (!name) return;
            const retryWindow =
                entry.aksStatus === "error" ? AKS_ERROR_RETRY_MS : MAX_AGE_MS;
            const aksIsStale = !entry.aksTs || Date.now() - entry.aksTs > retryWindow;
            if (aksIsStale) queueAksFetch(appid, name);
        });
    }

    // ---------- AllKeyShop API queue ----------
    function buildAksUrl(gameName) {
        return `${AKS_API_URL}?${AKS_STATIC_PARAMS}&search_name=${encodeURIComponent(gameName)}`;
    }

    function queueAksFetch(appid, gameName) {
        const cleanName = typeof gameName === "string" ? gameName.trim() : "";
        if (!cleanName || pendingAksFetch.has(appid)) return;
        pendingAksFetch.add(appid);
        aksQueue.push({ appid, gameName: cleanName });
        processAksQueue();
    }

    function processAksQueue() {
        if (aksQueueBusy || aksQueue.length === 0) return;
        aksQueueBusy = true;

        const { appid, gameName } = aksQueue.shift();
        if (!gameName) {
            pendingAksFetch.delete(appid);
            aksQueueBusy = false;
            setTimeout(processAksQueue, AKS_REQUEST_DELAY_MS);
            return;
        }
        const url = buildAksUrl(gameName);
        console.debug(
            "[WishlistMinPrice] Querying AllKeyShop:",
            gameName,
            "\n",
            url,
        );

        GM_xmlhttpRequest({
            method: "GET",
            url,
            headers: {
                Accept: "application/json",
                Referer: "https://www.allkeyshop.com/",
            },
            onload: function (res) {
                let conclusive = false;

                try {
                    const data = JSON.parse(res.responseText);
                    const product = data.products && data.products[0];
                    const offer = product && product.offers && product.offers[0];

                    if (
                        product &&
                        offer &&
                        typeof offer.price === "number" &&
                        isNameMatch(product.name, gameName)
                    ) {
                        if (
                            updateGamePrice(appid, {
                                aksPrice: offer.price,
                                name: gameName,
                            })
                        ) {
                            persistStore();
                            tryInject();
                        }
                    } else if (product) {
                        console.warn(
                            "[WishlistMinPrice] Discarded dubious match:",
                            gameName,
                            "->",
                            product.name,
                            "\n(paste the URL above in a new tab to check what it returns directly)",
                        );
                    }
                    // Valid JSON, with or without a match: conclusive, no early retry.
                    conclusive = true;
                } catch (e) {
                    console.warn(
                        "[WishlistMinPrice] Response is not valid JSON for",
                        gameName,
                        "- probably a temporary block/rate-limit, will retry in a few minutes",
                    );
                }

                const existing = store[appid] || {};
                store[appid] = {
                    ...existing,
                    aksTs: Date.now(),
                    aksStatus: conclusive ? "ok" : "error",
                };
                persistStore();
            },
            onerror: function (err) {
                console.warn(
                    "[WishlistMinPrice] Network error querying AllKeyShop for",
                    gameName,
                    "- will retry in a few minutes",
                    err,
                );
                const existing = store[appid] || {};
                store[appid] = { ...existing, aksTs: Date.now(), aksStatus: "error" };
                persistStore();
            },
            onloadend: function () {
                pendingAksFetch.delete(appid);
                aksQueueBusy = false;
                setTimeout(processAksQueue, AKS_REQUEST_DELAY_MS);
            },
        });
    }

    // Scans the currently rendered .Panel elements (Steam virtualizes them):
    // passively captures Steam's sale + original prices from the DOM (no scrolling)
    // and queues an AllKeyShop lookup by name when our price is stale.
    function scanVisiblePanels() {
        const panels = document.querySelectorAll("div.Panel");
        let changed = false;
        const namedGames = [];

        panels.forEach((panel) => {
            const info = extractGameInfo(panel);
            if (!info) return;

            const { appid, name } = info;
            sessionSeenIds.add(appid);

            const update = {};
            if (name) update.name = name;

            // Price capture needs a fully painted panel: an empty name means
            // the href already points to the next game while the price tag
            // still shows the previous one's — reading it would attach a
            // phantom price to the new appid. Games the API declared without
            // price never render a price tag, so any capture for them is
            // garbage as well.
            if (name) {
                const entryForPanel = store[appid] || {};
                const prices = extractSteamPrices(panel);
                const badgePercent = extractDiscountPercent(panel);
                // Diagnostics snapshot: what this panel actually rendered
                // (ground truth, never persisted; also what AS counts from).
                const snap = domSnapshot.get(appid) || {
                    tag: null,
                    badge: null,
                    seen: 0,
                };
                snap.seen += 1;
                if (prices.discounted !== null) snap.tag = prices.discounted;
                if (badgePercent !== null) snap.badge = badgePercent;
                domSnapshot.set(appid, snap);
                if (verboseCapture) {
                    log("capture", appid, `"${name}"`, "tag:", prices.discounted, "badge:", badgePercent);
                }
                const isNoPrice = entryForPanel.noPrice === true;
                // Fresh API data (IStoreBrowseService / appdetails) is
                // authoritative: on a long-open tab the panels can be stale
                // (a sale may have ended server-side since page load) or
                // mid-swap during virtualization, so DOM capture only fills
                // gaps and never overwrites a fresh API price. During an
                // in-flight refresh (post-reset) DOM writes pause entirely.
                const apiFresh =
                    typeof entryForPanel.apiTs === "number" &&
                    Date.now() - entryForPanel.apiTs < MAX_AGE_MS;
                if (!apiFresh && !isNoPrice && !domCaptureSuppressed) {
                    if (prices.discounted !== null) {
                        update.steamPrice = prices.discounted;
                        if (prices.original !== null) {
                            update.steamOriginalPrice = prices.original;
                        }
                        if (badgePercent !== null) {
                            update.discountPercent = badgePercent;
                        } else if (
                            typeof entryForPanel.discountPercent !== "number"
                        ) {
                            update.discountPercent = 0;
                        }
                        if (entryForPanel._noPriceMisses) {
                            const clean = { ...entryForPanel };
                            delete clean._noPriceMisses;
                            store[appid] = clean;
                        }
                    } else if (typeof entryForPanel.steamPrice === "number") {
                        const misses = (entryForPanel._noPriceMisses || 0) + 1;
                        if (misses >= 2) {
                            const clean = { ...entryForPanel, noPrice: true };
                            delete clean.steamPrice;
                            delete clean.steamOriginalPrice;
                            delete clean.discountPercent;
                            delete clean.price;
                            delete clean.ts;
                            delete clean._noPriceMisses;
                            store[appid] = clean;
                            changed = true;
                        } else {
                            store[appid] = { ...entryForPanel, _noPriceMisses: misses };
                            changed = true;
                        }
                    }
                }
            }

            if (Object.keys(update).length > 0) {
                if (updateGamePrice(appid, update)) changed = true;
            }

            // Empty name = panel read mid-update (href already points to the
            // new game but the title isn't painted yet): skip the lookup.
            const cachedName = store[appid] && store[appid].name;
            const nameForAks =
                name || (typeof cachedName === "string" ? cachedName.trim() : "");
            if (nameForAks) namedGames.push({ appid, name: nameForAks });
        });

        if (changed) persistStore();

        // DOM capture never blocks on the queue; the name is already
        // stored, so the lookup can't go out with an empty search_name.
        namedGames.forEach(({ appid, name }) => {
            const entry = store[appid];
            const retryWindow =
                entry && entry.aksStatus === "error" ? AKS_ERROR_RETRY_MS : MAX_AGE_MS;
            const aksIsStale =
                !entry || !entry.aksTs || Date.now() - entry.aksTs > retryWindow;
            if (aksIsStale) queueAksFetch(appid, name);
        });
    }

    // Totals across the cache in one pass:
    // - total: minimum value (min of Steam's price and AllKeyShop's offer)
    // - currentTotal: what Steam itself charges right now (its own
    //   discounts, incl. the bundle deals shown in the wishlist panels)
    // - originalTotal: pre-discount Steam prices (upper bound)
    // - onSaleCount / noPriceCount: wishlist stats, like the extensions show
    function computeTotals() {
        const ids = Object.keys(store);
        const now = Date.now();

        let total = 0;
        let currentTotal = 0;
        let originalTotal = 0;
        let freshCount = 0;
        let onSaleCount = 0;
        let noPriceCount = 0;

        ids.forEach((id) => {
            const entry = store[id];
            // Free-to-play games show no price tag in the panel; AugmentedSteam
            // counts them as "without price" (the bar should match AS).
            if (entry.is_free === true) {
                noPriceCount++;
                return;
            }
            const fresh = Boolean(entry.ts && now - entry.ts < MAX_AGE_MS);

            if (typeof entry.steamPrice === "number") {
                currentTotal += entry.steamPrice;

                // Only count games with a real Steam price in the minimum;
                // an aksPrice alone must not inflate it.
                if (typeof entry.price === "number") {
                    total += entry.price;
                    if (fresh) freshCount++;
                }

                // "On sale" uses Steam's own discount flag; a bundle deal
                // in the panel must not count as a sale. Legacy entries
                // without the field fall back to the price comparison.
                const onSale =
                    typeof entry.discountPercent === "number"
                        ? entry.discountPercent > 0
                        : typeof entry.steamOriginalPrice === "number" &&
                        entry.steamOriginalPrice > entry.steamPrice + 0.005;
                if (onSale) onSaleCount++;

                if (typeof entry.steamOriginalPrice === "number") {
                    originalTotal += entry.steamOriginalPrice;
                } else {
                    // Legacy cache entry (pre-3.5): until the next refresh,
                    // Steam's own price stands in so the original total
                    // never dips below current/minimum meanwhile.
                    originalTotal += entry.steamPrice;
                }
            } else {
                // No price known (unreleased, subscription, unavailable...).
                noPriceCount++;
            }
        });

        return {
            total,
            currentTotal,
            originalTotal,
            freshCount,
            onSaleCount,
            noPriceCount,
            storeSize: ids.length,
        };
    }

    // ---------- Stat injection / update ----------
    // Own stylesheet: Steam's hashed class names can't be reused reliably,
    // so the stat ships with self-contained tm-* styling matching the page
    // (Motiva Sans, blue #1a9fff labels, hairline divider like Steam's).
    function ensureStyles() {
        if (document.getElementById("tm-wishlist-min-styles")) return;
        const style = document.createElement("style");
        style.id = "tm-wishlist-min-styles";
        style.textContent =
            ".tm-min-bar{display:flex;align-items:center;flex-wrap:wrap;" +
            "gap:4px 16px;margin-top:8px;padding-top:8px;" +
            "border-top:1px solid rgba(255,255,255,.08);" +
            "font-family:'Motiva Sans',Arial,Helvetica,sans-serif}" +
            ".tm-min-bar .tm-min-group{display:flex;align-items:baseline;gap:6px}" +
            ".tm-min-bar .tm-min-price,.tm-min-bar .tm-min-count{font-weight:700;" +
            "color:#fff;font-size:15px;line-height:1.3;" +
            "font-variant-numeric:tabular-nums}" +
            ".tm-min-bar .tm-min-label{font-size:11px;color:#1a9fff;" +
            "text-transform:uppercase;letter-spacing:.5px}" +
            ".tm-min-bar .tm-min-sep{width:1px;height:14px;" +
            "background:rgba(255,255,255,.15)}" +
            ".tm-min-bar .tm-min-reset{cursor:pointer;opacity:.6;margin-left:2px;" +
            "transition:opacity .15s ease;background:none;border:none;padding:0;" +
            "font:inherit;color:inherit;line-height:1}" +
            ".tm-min-bar .tm-min-reset:hover{opacity:1}" +
            ".tm-min-bar .tm-min-reset:focus{outline:1px solid #1a9fff;outline-offset:2px}" +
            ".tm-min-bar .tm-min-reset:focus:not(:focus-visible){outline:none}";
        document.head.appendChild(style);
    }

    function injectMinStat(bar) {
        // DOM mode also captures visible panels on each injection; API mode
        // already has the data.
        if (!apiMode && domModeStarted) scanVisiblePanels();

        const {
            total,
            currentTotal,
            originalTotal,
            freshCount,
            onSaleCount,
            noPriceCount,
            storeSize,
        } = computeTotals();
        const wishlistTotal = apiWishlistTotal;

        // Reuse the row sitting right after the bar; drop stale copies that
        // React left behind after re-renders.
        let statDiv = null;
        document.querySelectorAll(".tm-min-bar").forEach((el) => {
            if (!statDiv && el.previousElementSibling === bar) {
                statDiv = el;
            } else {
                el.remove();
            }
        });

        if (!statDiv) {
            // Groups, cheapest-first: minimum (Steam vs AllKeyShop), current
            // (Steam's own prices in the wishlist) and original (pre-discount);
            // then wishlist stats: total, on sale, without price.
            const newGroup = () => {
                const group = document.createElement("span");
                group.className = "tm-min-group";
                const price = document.createElement("span");
                price.className = "tm-min-price";
                group.appendChild(price);
                return { group, price };
            };
            const addSeparator = () => {
                const sep = document.createElement("span");
                sep.className = "tm-min-sep";
                statDiv.appendChild(sep);
            };
            const addCountGroup = (key, label) => {
                const group = document.createElement("span");
                group.className = "tm-min-group";
                const value = document.createElement("span");
                value.className = "tm-min-count";
                value.dataset.tmKey = key;
                group.appendChild(value);
                const text = document.createElement("span");
                text.className = "tm-min-label";
                text.textContent = label;
                group.appendChild(text);
                statDiv.appendChild(group);
                return value;
            };

            statDiv = document.createElement("div");
            statDiv.className = "tm-min-bar";

            // 1) Minimum value + reset button.
            const min = newGroup();
            const minLabel = document.createElement("span");
            minLabel.className = "tm-min-label";

            const minLabelText = document.createElement("span");
            minLabelText.className = "tm-min-label-text";
            minLabel.appendChild(minLabelText);

            // Small reset button so the cache can be cleared without the console.
            // Left click: reloads the page (clean, verified refresh path).
            // Middle click (auxclick): refresh in place.
            const resetBtn = document.createElement("button");
            resetBtn.type = "button";
            resetBtn.className = "tm-min-reset";
            resetBtn.textContent = "⟲";
            resetBtn.title =
                "Refresh prices (reloads the page; middle-click refreshes in place)";
            resetBtn.setAttribute("aria-label", "Clear cached prices");
            const doReset = (e, mode) => {
                e.stopPropagation();
                e.preventDefault();
                const ok =
                    typeof unsafeWindow.confirm === "function"
                        ? unsafeWindow.confirm(
                            "Clear the prices and query again? Game names are kept.",
                        )
                        : confirm("Clear the prices and query again? Game names are kept.");
                if (ok) {
                    console.log("[WishlistMinPrice] Reset clicked");
                    resetCache({ reload: mode !== "inplace" });
                }
            };
            resetBtn.addEventListener("click", (e) => doReset(e, "reload"));
            resetBtn.addEventListener("auxclick", (e) => doReset(e, "inplace"));
            minLabel.appendChild(resetBtn);

            min.group.appendChild(minLabel);
            statDiv.appendChild(min.group);

            addSeparator();

            // 2) Current value (Steam's own wishlist prices).
            const current = newGroup();
            const currentLabel = document.createElement("span");
            currentLabel.className = "tm-min-label";
            currentLabel.textContent = "current value";
            current.group.appendChild(currentLabel);
            statDiv.appendChild(current.group);

            addSeparator();

            // 3) Original value (pre-discount).
            const orig = newGroup();
            const origLabel = document.createElement("span");
            origLabel.className = "tm-min-label";
            origLabel.textContent = "original value";
            orig.group.appendChild(origLabel);
            statDiv.appendChild(orig.group);

            // 4) Wishlist stats.
            addSeparator();
            addCountGroup("wishlist", "on wishlist");
            addSeparator();
            addCountGroup("sale", "on sale");
            addSeparator();
            addCountGroup("noprice", "without price");

            bar.insertAdjacentElement("afterend", statDiv);
        }

        // Only touch the DOM when a value actually changed: assigning
        // textContent unconditionally would mutate the page, re-trigger the
        // observer and keep the row "updating" forever.
        const setText = (el, text) => {
            if (el.textContent !== text) el.textContent = text;
        };

        const priceEls = statDiv.querySelectorAll(".tm-min-price");
        setText(priceEls[0], formatPrice(total));
        setText(priceEls[1], formatPrice(currentTotal));
        setText(priceEls[2], formatPrice(originalTotal));

        const gameTotal = wishlistTotal !== null ? wishlistTotal : storeSize;
        setText(
            statDiv.querySelector('[data-tm-key="wishlist"]'),
            String(gameTotal),
        );
        setText(statDiv.querySelector('[data-tm-key="sale"]'), String(onSaleCount));
        setText(
            statDiv.querySelector('[data-tm-key="noprice"]'),
            String(noPriceCount),
        );

        const minLabelText = statDiv.querySelector(".tm-min-label-text");
        setText(
            minLabelText,
            wishlistTotal
                ? `minimum value (${freshCount}/${wishlistTotal})`
                : "minimum value",
        );
    }

    function tryInject() {
        // Steam's controls bar, found structurally instead of by hashed
        // class names: the search box is the page's only <input> that is a
        // direct child of a .Panel (the Options/Sort popovers nest theirs
        // inside <label>/<form>), whatever the locale.
        const searchInput = document.querySelector("div.Panel > input");
        const bar = searchInput ? searchInput.parentElement : null;
        if (bar) injectMinStat(bar);
    }

    function inject() {
        tryInject();
    }

    // ---------- Observers ----------
    let scanTimeout = null;
    const scanObserver = new MutationObserver(() => {
        clearTimeout(scanTimeout);
        scanTimeout = setTimeout(scanVisiblePanels, 100);
    });

    let injectTimeout = null;
    const injectObserver = new MutationObserver(() => {
        clearTimeout(injectTimeout);
        injectTimeout = setTimeout(tryInject, 50);
    });

    // DOM-scraping fallback; only started if the Steam API fails (private
    // wishlist, timeout) or there's no steamid.
    function startDomMode() {
        if (domModeStarted) return;
        domModeStarted = true;
        log("DOM mode active (API unavailable or no steamid)");
        setInterval(scanVisiblePanels, POLL_INTERVAL_MS);
    }

    function init() {
        const steamid = resolveSteamId();
        storageKey = getStorageKey(steamid);
        loadStore();
        log(`v${SCRIPT_VERSION} ready (key=${storageKey}, entries=${Object.keys(store).length})`);

        let migrated = false;
        Object.keys(store).forEach((id) => {
            const entry = store[id];
            if (
                entry.bundlePrice !== undefined ||
                entry.bundleTs !== undefined ||
                entry.bundleStatus !== undefined
            ) {
                delete entry.bundlePrice;
                delete entry.bundleTs;
                delete entry.bundleStatus;
                migrated = true;
            }
        });
        if (migrated) persistStore();

        // Injection observer is common to both modes: reacts to DOM changes
        // (e.g. Steam's controls bar appearing).
        ensureStyles();
        injectObserver.observe(document.body, {
            childList: true,
            subtree: true,
            characterData: true,
        });

        // Passive panel capture (no scrolling). IStoreBrowseService already provides
        // the correct price incl. bundles; the observer only supplements names/AKS
        // as panels render during normal browsing.
        scanObserver.observe(document.body, {
            childList: true,
            subtree: true,
            characterData: true,
        });

        if (steamid) {
            refreshFromApi(steamid);
        } else {
            startDomMode();
        }

        // First inject on load: shows the cache while fresh API data arrives
        tryInject();
    }

    init();
})();
