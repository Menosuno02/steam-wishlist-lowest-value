// ==UserScript==
// @name         Steam Wishlist Lowest Value
// @namespace    http://tampermonkey.net/
// @version      3.3
// @description  Shows the total minimum price of your wishlist: compares the price shown by Steam (incl. bundle pricing: each wishlist panel shows your real price, own discount + bundle discount) with AllKeyShop's price (queried directly from its API) and adds it next to the Augmented Steam stats. The wishlist comes from the official Steam API; prices are captured by auto-sweeping the virtualized list (aborts if you scroll); DOM scraping is the fallback when the API fails (private wishlist, timeout, etc.).
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

    // Country/language for appdetails prices (cc=es -> EUR).
    const STEAM_CC = "es";
    const STEAM_LANG = "es";
    const WISHLIST_API_URL =
        "https://api.steampowered.com/IWishlistService/GetWishlist/v1/";
    const APPDETAILS_URL = "https://store.steampowered.com/api/appdetails";
    // appdetails accepts many appids per call, but batch to stay under URL length limits.
    const PRICE_BATCH_SIZE = 50;
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
    const AKS_REQUEST_DELAY_MS = 100;
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
    const sessionSeenIds = new Set();
    const pendingAksFetch = new Set();
    const aksQueue = [];
    let aksQueueBusy = false;
    const pendingNameFetch = new Set();
    const nameQueue = [];
    let nameQueueActive = 0;

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

    function resetCache() {
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
        persistStore();
        console.log("[WishlistMinPrice] Prices cleared (names kept)");

        const steamid = resolveSteamId();
        if (steamid) {
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

    function extractSteamPrice(panel) {
        const el = panel.querySelector(".-OkCLv-56oQ- .-HQzBzl6lqI-");
        return el ? parsePrice(el.textContent) : null;
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

    // Merge known data with the new price and recompute the minimum.
    function updateGamePrice(appid, { steamPrice, aksPrice, name } = {}) {
        const existing = store[appid] || {};
        const merged = { ...existing };
        let changed = false;

        if (steamPrice !== undefined) {
            changed = existing.steamPrice !== steamPrice || changed;
            merged.steamPrice = steamPrice;
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
        for (let i = 0; i < appids.length; i += PRICE_BATCH_SIZE) {
            const chunk = appids.slice(i, i + PRICE_BATCH_SIZE);
            const url =
                `${APPDETAILS_URL}?appids=${chunk.join(",")}&cc=${STEAM_CC}` +
                `&l=${STEAM_LANG}&filters=price_overview`;
            const res = await steamFetch(url, { retries: 1 });
            let changed = false;

            if (res.ok && res.json) {
                chunk.forEach((appid) => {
                    const info = res.json[appid];
                    if (!info || info.success !== true) return;

                    const d = info.data;
                    const p = d && !Array.isArray(d) ? d.price_overview : null;
                    if (p && typeof p.final === "number") {
                        changed =
                            updateGamePrice(appid, { steamPrice: p.final / 100 }) || changed;
                        return;
                    }
                    // No price_overview (free, subscription, unavailable):
                    // if is_free is unknown, resolve it via basic.
                    const entry = store[appid] || {};
                    if (entry.is_free === true && typeof entry.steamPrice !== "number") {
                        changed = updateGamePrice(appid, { steamPrice: 0 }) || changed;
                    } else if (typeof entry.is_free !== "boolean") {
                        queueNameFetch(appid);
                    }
                });
            }

            if (changed) persistStore();
            inject();
        }
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
        const url =
            `${APPDETAILS_URL}?appids=${appid}&cc=${STEAM_CC}&l=${STEAM_LANG}` +
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
                changed = updateGamePrice(appid, { steamPrice: 0 }) || changed;
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
        const items = await fetchWishlist(steamid);
        if (!items) {
            console.warn(
                "[WishlistMinPrice] Could not read the wishlist via the API " +
                "(private wishlist or timeout?), falling back to DOM mode",
            );
            startDomMode();
            tryInject();
            return;
        }

        apiMode = true;
        const appids = items.map((i) => String(i.appid));
        apiWishlistTotal = appids.length;

        reconcileCache(appids);

        // New games (no known name yet): one basic call each.
        appids.forEach((appid) => {
            if (!store[appid] || !store[appid].name) queueNameFetch(appid);
        });

        queueAksForStale();
        inject();

        await fetchPricesBatch(appids);
        // Sweep the virtualized list to capture each game's real minimum
        // (incl. bundle pricing, which the panels already show); aborts only
        // if the user scrolls. Games it misses keep the API price.
        startSweep(appids);
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

    // ---------- Wishlist sweep (minimum prices incl. bundles) ----------
    // Each panel shows the real minimum on Steam (own discount + bundle base
    // when completing a set). The list is virtualized, so we scroll
    // programmatically to the end to capture all panels, no /bundlelist calls.
    const SWEEP_STEP_DELAY_MS = 400;
    const SWEEP_MAX_IDLE_STEPS = 3;

    const sweepState = { active: false, aborted: false, expectedTop: 0 };

    function sleep(ms) {
        return new Promise((resolve) => setTimeout(resolve, ms));
    }

    // Waits one sweep step, pausing while the tab is hidden.
    async function waitSweepStep() {
        let waited = 0;
        while (waited < SWEEP_STEP_DELAY_MS) {
            if (document.hidden) {
                await sleep(300);
                continue;
            }
            await sleep(Math.min(100, SWEEP_STEP_DELAY_MS - waited));
            waited += 100;
        }
    }

    // Scrolls through the virtualized wishlist capturing all panels. Aborts
    // as soon as the user scrolls (captured data stays; the rest keeps the
    // API price). Restores the scroll position when done without abort.
    async function startSweep(appids) {
        if (sweepState.active || appids.length === 0) return;
        sweepState.active = true;
        sweepState.aborted = false;

        const scroller = document.scrollingElement || document.documentElement;
        const initialTop = scroller.scrollTop;
        sweepState.expectedTop = initialTop;

        const onScroll = () => {
            // Our own scroll fires the event right after setting expectedTop;
            // any deviation means the user moved the page.
            if (Math.abs(scroller.scrollTop - sweepState.expectedTop) > 4) {
                sweepState.aborted = true;
            }
        };
        window.addEventListener("scroll", onScroll, { passive: true });

        try {
            scanVisiblePanels();
            const wanted = new Set(appids);
            let idleSteps = 0;

            while (
                !sweepState.aborted &&
                idleSteps < SWEEP_MAX_IDLE_STEPS &&
                ![...wanted].every((id) => sessionSeenIds.has(id))
            ) {
                const before = sessionSeenIds.size;
                const maxTop = scroller.scrollHeight - window.innerHeight;
                const target = Math.min(
                    scroller.scrollTop + window.innerHeight * 0.9,
                    maxTop,
                );
                sweepState.expectedTop = target;
                scroller.scrollTop = target;
                await waitSweepStep();
                scanVisiblePanels();
                idleSteps = sessionSeenIds.size === before ? idleSteps + 1 : 0;
            }

            console.log(
                `[WishlistMinPrice] Sweep finished: ${sessionSeenIds.size}/${appids.length} games captured` +
                (sweepState.aborted ? " (aborted: you scrolled)" : ""),
            );
        } finally {
            window.removeEventListener("scroll", onScroll);
            if (!sweepState.aborted && scroller.scrollTop !== initialTop) {
                scroller.scrollTop = initialTop;
            }
            sweepState.active = false;
            inject();
        }
    }

    // Scans the currently rendered .Panel elements (Steam virtualizes them
    // on scroll): captures the Steam price from the DOM and queues an
    // AllKeyShop lookup by name when our price for that game is stale.
    function scanVisiblePanels() {
        const panels = document.querySelectorAll("div.Panel");
        let changed = false;
        const namedGames = [];

        panels.forEach((panel) => {
            const info = extractGameInfo(panel);
            if (!info) return;

            const { appid, name } = info;
            sessionSeenIds.add(appid);

            const steamPrice = extractSteamPrice(panel);
            const update = {};
            if (steamPrice !== null) update.steamPrice = steamPrice;
            if (name) update.name = name;

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

    // ---------- Wishlist total count (DOM mode only) ----------
    function getWishlistTotalCount() {
        const stats = document.querySelectorAll(
            ".stats.svelte-1vzkkpc .stat.svelte-1vzkkpc",
        );
        for (const stat of stats) {
            const label = stat.querySelector(".label");
            if (label && label.textContent.trim() === "on wishlist") {
                const n = parseInt(stat.textContent.replace(/\D/g, ""), 10);
                return isNaN(n) ? null : n;
            }
        }
        return null;
    }

    function computeMinimumTotal() {
        const ids = Object.keys(store);
        const now = Date.now();

        let total = 0;
        let freshCount = 0;

        ids.forEach((id) => {
            const entry = store[id];
            // Only count games with a real Steam price; aksPrice alone must
            // not inflate the wishlist minimum.
            if (typeof entry.price !== "number") return;
            if (typeof entry.steamPrice !== "number") return;
            total += entry.price;
            if (entry.ts && now - entry.ts < MAX_AGE_MS) freshCount++;
        });

        return { total, freshCount };
    }

    // ---------- Stat injection / update ----------
    function injectMinStat(statsContainer) {
        // DOM mode also captures visible panels on each injection; API mode
        // already has the data.
        if (!apiMode && domModeStarted) scanVisiblePanels();

        const { total, freshCount } = computeMinimumTotal();
        const wishlistTotal =
            apiWishlistTotal !== null ? apiWishlistTotal : getWishlistTotalCount();

        let statDiv = statsContainer.querySelector(".tm-min-value-stat");
        if (!statDiv) {
            statDiv = document.createElement("div");
            statDiv.className = "stat svelte-1vzkkpc tm-min-value-stat";
            statDiv.appendChild(document.createTextNode(""));

            const label = document.createElement("span");
            label.className = "label svelte-1vzkkpc";

            const labelText = document.createElement("span");
            labelText.className = "tm-min-label-text";
            label.appendChild(labelText);

            // Small reset button so the cache can be cleared without the console
            const resetBtn = document.createElement("span");
            resetBtn.textContent = " ⟲";
            resetBtn.title = "Clear cached minimum prices";
            resetBtn.style.cursor = "pointer";
            resetBtn.style.opacity = "0.6";
            resetBtn.addEventListener("mouseenter", () => {
                resetBtn.style.opacity = "1";
            });
            resetBtn.addEventListener("mouseleave", () => {
                resetBtn.style.opacity = "0.6";
            });
            resetBtn.addEventListener("click", (e) => {
                e.stopPropagation();
                e.preventDefault();
                if (confirm("Clear the prices and query again? Game names are kept.")) {
                    resetCache();
                }
            });
            label.appendChild(resetBtn);

            statDiv.appendChild(label);

            const stats = Array.from(statsContainer.children);
            const currentValueStat = stats.find((el) => {
                const lbl = el.querySelector(".label");
                return lbl && lbl.textContent.trim() === "current value";
            });

            if (currentValueStat) {
                currentValueStat.insertAdjacentElement("afterend", statDiv);
            } else {
                statsContainer.insertBefore(statDiv, statsContainer.firstChild);
            }
        }

        statDiv.childNodes[0].textContent = formatPrice(total);

        const labelText = statDiv.querySelector(".tm-min-label-text");
        labelText.textContent = wishlistTotal
            ? `minimum value (${freshCount}/${wishlistTotal})`
            : "minimum value";
    }

    function tryInject() {
        const statsContainer = document.querySelector(".stats.svelte-1vzkkpc");
        if (statsContainer) {
            injectMinStat(statsContainer);
        }
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
        console.log("[WishlistMinPrice] DOM mode (fallback) active");
        scanObserver.observe(document.body, {
            childList: true,
            subtree: true,
            characterData: true,
        });
        setInterval(scanVisiblePanels, POLL_INTERVAL_MS);
    }

    function init() {
        const steamid = resolveSteamId();
        storageKey = getStorageKey(steamid);
        loadStore();

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
        // (e.g. the Augmented Steam stats container appearing).
        injectObserver.observe(document.body, {
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
