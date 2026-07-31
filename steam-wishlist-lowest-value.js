// ==UserScript==
// @name         Steam Wishlist Lowest Value
// @namespace    http://tampermonkey.net/
// @version      2.1
// @description  Calcula el precio mínimo total de tu wishlist comparando el precio en Steam con el precio de AllKeyShop (consultado directamente a su API, sin depender de su extensión) y lo añade junto a las stats de Augmented Steam. Usa un caché persistente porque Steam virtualiza los elementos de la lista al hacer scroll.
// @author       Menosuno02
// @match        https://store.steampowered.com/wishlist/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=steampowered.com
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      www.allkeyshop.com
// @run-at       document-idle
// ==/UserScript==

(function () {
    "use strict";

    // Caché por URL de wishlist (por si se usa en varios perfiles)
    const STORAGE_KEY = "wishlistMinPrices::" + location.pathname;

    // Cuánto tiempo se considera "fresco" el precio de un juego antes de
    // volver a consultarlo / dejar de contarlo como "reciente" en el
    // indicador de cobertura. Se usa tanto para el precio de Steam como
    // para decidir cuándo volver a pedirle el precio a AllKeyShop.
    const MAX_AGE_MS = 24 * 60 * 60 * 1000; // 1 día

    // Cada cuánto revisamos los paneles visibles "por si acaso", además de
    // cuando el MutationObserver detecta cambios. Sirve sobre todo para
    // detectar paneles nuevos mientras scrolleas rápido.
    const POLL_INTERVAL_MS = 400;

    // Delay entre peticiones a la API de AllKeyShop. Es un endpoint interno
    // no documentado (pensado para el ritmo de su propia extensión), así
    // que mejor no bombardearlo. Súbelo si ves errores/bloqueos, bájalo si
    // vas con prisa y no te importa el riesgo.
    const AKS_REQUEST_DELAY_MS = 800;
    // Si una petición falla (bloqueo temporal, respuesta no-JSON, error de
    // red) no lo tratamos como "ya consultado" durante 24h — reintentamos
    // mucho antes, porque lo más probable es que sea un bloqueo puntual.
    const AKS_ERROR_RETRY_MS = 5 * 60 * 1000; // 5 minutos
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
    const sessionSeenIds = new Set();
    const pendingAksFetch = new Set();
    const aksQueue = [];
    let aksQueueBusy = false;

    // ---------- Carga del caché persistente ----------
    try {
        store = JSON.parse(GM_getValue(STORAGE_KEY, "{}")) || {};
    } catch (e) {
        store = {};
    }

    function persistStore() {
        try {
            GM_setValue(STORAGE_KEY, JSON.stringify(store));
        } catch (e) {
            console.warn("[WishlistMinPrice] No se pudo guardar el caché", e);
        }
    }

    function resetCache() {
        store = {};
        sessionSeenIds.clear();
        pendingAksFetch.clear();
        aksQueue.length = 0;
        persistStore();
        console.log("[WishlistMinPrice] Caché borrado");
        scanVisiblePanels();
        tryInject();
    }

    // Ejecuta en la consola: __wishlistMinPriceReset()
    // Colgado de unsafeWindow (no de window): con @grant GM_* el script corre
    // en un sandbox, así que "window" ahí no es el window real de la página.
    unsafeWindow.__wishlistMinPriceReset = resetCache;

    // Depuración: __wishlistMinPriceDebug() vuelca en consola los N juegos
    // con el "price" más alto (por defecto 20), con su steamPrice/aksPrice
    // por separado, para detectar valores sospechosos.
    unsafeWindow.__wishlistMinPriceDebug = function (limit = 20) {
        const rows = Object.entries(store).map(([appid, v]) => ({
            appid,
            name: v.name || "(sin nombre)",
            steamPrice: typeof v.steamPrice === "number" ? v.steamPrice : null,
            aksPrice: typeof v.aksPrice === "number" ? v.aksPrice : null,
            price: typeof v.price === "number" ? v.price : null,
            ts: v.ts ? new Date(v.ts).toLocaleString() : null,
        }));
        rows.sort((a, b) => (b.price || 0) - (a.price || 0));
        console.table(rows.slice(0, limit));
        console.log(`Total entradas en caché: ${rows.length}`);
        return rows;
    };

    // Depuración: __wishlistMinPriceMissingSteam() lista los juegos para los
    // que NUNCA hemos capturado un steamPrice por DOM (solo tenemos aksPrice,
    // sin ningún tope real de Steam).
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
            `Juegos sin steamPrice capturado: ${rows.length} de ${Object.keys(store).length}`,
        );
        return rows;
    };

    // Depuración: __wishlistMinPriceExtras() lista entradas del caché que NO
    // se han visto en la sesión actual — si ya has scrolleado toda la lista,
    // son candidatas a ser restos de juegos quitados de la wishlist (o algún
    // fallo de virtualización que mezcló datos de dos juegos distintos).
    unsafeWindow.__wishlistMinPriceExtras = function () {
        const extras = Object.keys(store).filter((id) => !sessionSeenIds.has(id));
        console.log(
            `En caché pero NO vistos en esta sesión: ${extras.length} de ${Object.keys(store).length} en caché total`,
        );
        console.table(
            extras.map((id) => ({
                appid: id,
                name: store[id].name || "(sin nombre)",
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

    // ---------- Extracción de datos por juego ----------
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

        // Durante la virtualización Steam puede actualizar primero el href y
        // pintar el texto después. Solo usamos nombres del mismo appid, para no
        // mezclar el título anterior del panel con el juego nuevo.
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

    // Compara nombres de forma laxa para evitar aceptar un precio de un
    // juego distinto que la API haya devuelto como "más relevante".
    // Maneja los casos típicos: números romanos vs arábigos (VI vs 6),
    // apóstrofes (don't vs dont), símbolos de marca, y subtítulos/prefijos
    // que un lado tiene y el otro no (basta con que la mayoría de palabras
    // del título más corto aparezcan en el más largo).
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
            .replace(/['’]/g, "") // don't -> dont, meier's -> meiers
            .replace(/[™®©]/g, "") // símbolos de marca
            .replace(/[^a-z0-9]+/g, " ") // resto de puntuación -> espacio
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

    // Combina lo que ya sabíamos de un juego con el dato nuevo (precio de
    // Steam y/o de AllKeyShop) y recalcula el mínimo
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

    // ---------- Cola de peticiones a la API de AllKeyShop ----------
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
            "[WishlistMinPrice] Consultando AllKeyShop:",
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
                            "[WishlistMinPrice] Descartado match dudoso:",
                            gameName,
                            "->",
                            product.name,
                            "\n(pega la URL de arriba en una pestaña nueva para comprobar qué devuelve directamente)",
                        );
                    }
                    // Si llegamos aquí, la respuesta era JSON válido: sea con
                    // match, sin match, o sin producto, es un resultado
                    // concluyente y no hace falta reintentarlo pronto.
                    conclusive = true;
                } catch (e) {
                    console.warn(
                        "[WishlistMinPrice] Respuesta no es JSON válido para",
                        gameName,
                        "- probablemente bloqueo/rate-limit temporal, se reintentará en unos minutos",
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
                    "[WishlistMinPrice] Error de red consultando AllKeyShop para",
                    gameName,
                    "- se reintentará en unos minutos",
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

    // Recorre los .Panel actualmente renderizados (Steam los virtualiza al
    // hacer scroll): captura el precio de Steam directamente del DOM, y
    // dispara una consulta propia a AllKeyShop por nombre si no tenemos un
    // precio suyo reciente para ese juego
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

            // Si el nombre viene vacío es que hemos leído el panel a medio
            // actualizar (típico al scrollear rápido en una lista virtualizada:
            // el href ya apunta al juego nuevo pero el texto del título
            // todavía no se ha pintado). No lo tratamos como "sin nombre real",
            // simplemente no consultamos nada y esperamos al siguiente escaneo.
            const cachedName = store[appid] && store[appid].name;
            const nameForAks =
                  name || (typeof cachedName === "string" ? cachedName.trim() : "");
            if (nameForAks) namedGames.push({ appid, name: nameForAks });
        });

        if (changed) persistStore();

        // No se bloquea la captura del DOM por la cola ni por la red. Para cuando
        // llegamos aquí, el nombre ya está guardado y la consulta jamás puede
        // salir con search_name vacío.
        namedGames.forEach(({ appid, name }) => {
            const entry = store[appid];
            const retryWindow =
                  entry && entry.aksStatus === "error" ? AKS_ERROR_RETRY_MS : MAX_AGE_MS;
            const aksIsStale =
                  !entry || !entry.aksTs || Date.now() - entry.aksTs > retryWindow;
            if (aksIsStale) queueAksFetch(appid, name);
        });
    }

    // ---------- Lectura del total de la wishlist (para saber la cobertura del caché) ----------
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
            if (typeof entry.price !== "number") return;
            total += entry.price;
            if (entry.ts && now - entry.ts < MAX_AGE_MS) freshCount++;
        });

        return { total, freshCount };
    }

    // ---------- Inyección / actualización del stat ----------
    function injectMinStat(statsContainer) {
        scanVisiblePanels(); // capturamos también lo que hay visible justo ahora

        const { total, freshCount } = computeMinimumTotal();
        const wishlistTotal = getWishlistTotalCount();

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

            // Miniboton para vaciar el caché sin tener que usar la consola
            const resetBtn = document.createElement("span");
            resetBtn.textContent = " ⟲";
            resetBtn.title = "Vaciar caché de precios mínimos";
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
                if (
                    confirm(
                        "¿Vaciar el caché de precios mínimos? Tendrás que volver a scrollear la wishlist para reconstruirlo.",
                    )
                ) {
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

    // ---------- Observadores ----------
    let scanTimeout = null;
    const scanObserver = new MutationObserver(() => {
        clearTimeout(scanTimeout);
        scanTimeout = setTimeout(scanVisiblePanels, 100);
    });
    scanObserver.observe(document.body, {
        childList: true,
        subtree: true,
        characterData: true,
    });

    let injectTimeout = null;
    const injectObserver = new MutationObserver(() => {
        clearTimeout(injectTimeout);
        injectTimeout = setTimeout(tryInject, 50);
    });
    injectObserver.observe(document.body, {
        childList: true,
        subtree: true,
        characterData: true,
    });

    // Poll de refuerzo: revisa paneles visibles cada pocos ms además de las
    // mutaciones detectadas, para no perder juegos al scrollear rápido.
    setInterval(scanVisiblePanels, POLL_INTERVAL_MS);

    // Primer intento al cargar la página
    scanVisiblePanels();
    tryInject();
})();
