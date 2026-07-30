// ==UserScript==
// @name         Steam Wishlist Lowest Value
// @namespace    http://tampermonkey.net/
// @version      1.3
// @description  Calcula el precio mínimo total de tu wishlist (comparando el mejor precio encontrado en la extensión de AllKeyShop con el precio en Steam) y lo añade junto a las stats de Augmented Steam. Usa un caché persistente porque Steam virtualiza los elementos de la lista al hacer scroll.
// @author       Menosuno02
// @match        https://store.steampowered.com/wishlist/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=steampowered.com
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        unsafeWindow
// @run-at       document-idle
// ==/UserScript==


(function () {
    'use strict';

    // Caché por URL de wishlist (por si se usa en varios perfiles)
    const STORAGE_KEY = 'wishlistMinPrices::' + location.pathname;

    // Cuánto tiempo se considera "fresco" el precio de un juego antes de
    // marcarlo como pendiente de refrescar (no se elimina, solo deja de
    // contar como "reciente" en el indicador de cobertura). Ajusta este
    // valor según lo activo que esté en rebajas: en plena Steam Sale,
    // conviene bajarlo (p. ej. 12h); fuera de rebajas, los precios apenas
    // cambian y puedes subirlo sin problema.
    const MAX_AGE_MS = 24 * 60 * 60 * 1000; // 1 día

    // Cada cuánto revisamos los paneles visibles "por si acaso", además de
    // cuando el MutationObserver detecta cambios. Esto es lo que de verdad
    // soluciona que se pierdan juegos al scrollear rápido: el precio de
    // AllKeyShop/Augmented Steam tarda un poco en cargar de forma asíncrona
    // tras montarse el panel, y si Steam lo virtualiza (destruye) antes de
    // que llegue el dato, un observer más rápido no sirve de nada — hace
    // falta seguir mirando mientras el panel siga vivo.
    const POLL_INTERVAL_MS = 400;

    let currencySymbol = '€';
    let store = {};
    const sessionSeenIds = new Set();

    // Carga del caché persistente
    try {
        store = JSON.parse(GM_getValue(STORAGE_KEY, '{}')) || {};
    } catch (e) {
        store = {};
    }

    function persistStore() {
        try {
            GM_setValue(STORAGE_KEY, JSON.stringify(store));
        } catch (e) {
            console.warn('[WishlistMinPrice] No se pudo guardar el caché', e);
        }
    }

    function resetCache() {
        store = {};
        sessionSeenIds.clear();
        persistStore();
        console.log('[WishlistMinPrice] Caché borrado');
        scanVisiblePanels();
        tryInject();
    }

    // Por si algún día quieres limpiar el caché (juegos quitados de la wishlist, etc.)
    // Ejecuta en la consola: __wishlistMinPriceReset()
    // OJO: se cuelga de unsafeWindow (no de window) porque con @grant GM_*
    // Tampermonkey ejecuta el script en un sandbox; "window" ahí no es el
    // window real de la página, así que la consola del navegador (que sí
    // opera sobre la página real) nunca lo vería.
    unsafeWindow.__wishlistMinPriceReset = resetCache;

    // Parseo / formato de precios
    function extractCurrencySymbol(text) {
        if (!text) return null;
        const match = text.match(/[^\d,.\s-]+/);
        return match ? match[0].trim() : null;
    }

    function parsePrice(text) {
        if (!text) return null;

        const symbol = extractCurrencySymbol(text);
        if (symbol) currencySymbol = symbol;

        let cleaned = text.replace(/[^\d,.\-]/g, '').trim();
        if (!cleaned) return null;

        const lastComma = cleaned.lastIndexOf(',');
        const lastDot = cleaned.lastIndexOf('.');
        let decimalSep = null;

        if (lastComma > -1 && lastDot > -1) {
            decimalSep = lastComma > lastDot ? ',' : '.';
        } else if (lastComma > -1) {
            decimalSep = ',';
        } else if (lastDot > -1) {
            decimalSep = '.';
        }

        if (decimalSep) {
            const thousandSep = decimalSep === ',' ? '.' : ',';
            cleaned = cleaned.split(thousandSep).join('');
            cleaned = cleaned.replace(decimalSep, '.');
        }

        const value = parseFloat(cleaned);
        return isNaN(value) ? null : value;
    }

    function formatPrice(value) {
        return value
            .toLocaleString('de-DE', { minimumFractionDigits: 2, maximumFractionDigits: 2 })
            .replace(/\./g, ' ') + currencySymbol;
    }

    // Extracción de datos por juego
    function extractAppId(panel) {
        const link = panel.querySelector('a[href*="/app/"]');
        if (!link) return null;
        const match = link.href.match(/\/app\/(\d+)/);
        return match ? match[1] : null;
    }

    function extractMinPriceFromPanel(panel) {
        const priceContainer = panel.querySelector('div.S2Q8eqrNOA4-');
        if (!priceContainer) return null;

        const bestPriceEl = priceContainer.querySelector('.discount_final_price');
        const steamPriceEl = priceContainer.querySelector('.-OkCLv-56oQ- .-HQzBzl6lqI-');

        const bestPrice = parsePrice(bestPriceEl ? bestPriceEl.textContent : null);
        const steamPrice = parsePrice(steamPriceEl ? steamPriceEl.textContent : null);

        const candidates = [bestPrice, steamPrice].filter(v => v !== null);
        if (candidates.length === 0) return null;

        return Math.min(...candidates);
    }

    // Recorre los .Panel actualmente renderizados (Steam los virtualiza al hacer scroll)
    // y va guardando/actualizando su precio en el caché persistente
    function scanVisiblePanels() {
        const panels = document.querySelectorAll('div.Panel');
        let changed = false;

        panels.forEach(panel => {
            const appid = extractAppId(panel);
            if (!appid) return;

            const minPrice = extractMinPriceFromPanel(panel);
            if (minPrice === null) return;

            sessionSeenIds.add(appid);

            const existing = store[appid];
            if (!existing || existing.price !== minPrice) {
                store[appid] = { price: minPrice, ts: Date.now() };
                changed = true;
            }
        });

        if (changed) persistStore();
    }

    // Lectura del total de la wishlist (para saber la cobertura del caché)
    function getWishlistTotalCount() {
        const stats = document.querySelectorAll('.stats.svelte-1vzkkpc .stat.svelte-1vzkkpc');
        for (const stat of stats) {
            const label = stat.querySelector('.label');
            if (label && label.textContent.trim() === 'on wishlist') {
                const n = parseInt(stat.textContent.replace(/\D/g, ''), 10);
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

        ids.forEach(id => {
            total += store[id].price; // el precio cacheado se usa siempre, aunque esté desactualizado
            if (now - store[id].ts < MAX_AGE_MS) freshCount++;
        });

        return { total, cachedCount: ids.length, freshCount };
    }

    // Inyección / actualización del stat
    function injectMinStat(statsContainer) {
        scanVisiblePanels(); // capturamos también lo que hay visible justo ahora

        const { total, freshCount } = computeMinimumTotal();
        const wishlistTotal = getWishlistTotalCount();

        let statDiv = statsContainer.querySelector('.tm-min-value-stat');
        if (!statDiv) {
            statDiv = document.createElement('div');
            statDiv.className = 'stat svelte-1vzkkpc tm-min-value-stat';
            statDiv.appendChild(document.createTextNode(''));

            const label = document.createElement('span');
            label.className = 'label svelte-1vzkkpc';

            const labelText = document.createElement('span');
            labelText.className = 'tm-min-label-text';
            label.appendChild(labelText);

            // Miniboton para vaciar el caché sin tener que usar la consola
            const resetBtn = document.createElement('span');
            resetBtn.textContent = ' ⟲';
            resetBtn.title = 'Vaciar caché de precios mínimos';
            resetBtn.style.cursor = 'pointer';
            resetBtn.style.opacity = '0.6';
            resetBtn.addEventListener('mouseenter', () => { resetBtn.style.opacity = '1'; });
            resetBtn.addEventListener('mouseleave', () => { resetBtn.style.opacity = '0.6'; });
            resetBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                e.preventDefault();
                if (confirm('¿Vaciar el caché de precios mínimos? Tendrás que volver a scrollear la wishlist para reconstruirlo.')) {
                    resetCache();
                }
            });
            label.appendChild(resetBtn);

            statDiv.appendChild(label);

            const stats = Array.from(statsContainer.children);
            const currentValueStat = stats.find(el => {
                const lbl = el.querySelector('.label');
                return lbl && lbl.textContent.trim() === 'current value';
            });

            if (currentValueStat) {
                currentValueStat.insertAdjacentElement('afterend', statDiv);
            } else {
                statsContainer.insertBefore(statDiv, statsContainer.firstChild);
            }
        }

        statDiv.childNodes[0].textContent = formatPrice(total);

        const labelText = statDiv.querySelector('.tm-min-label-text');
        labelText.textContent = wishlistTotal
            ? `minimum value (${freshCount}/${wishlistTotal})`
            : 'minimum value';
    }

    function tryInject() {
        const statsContainer = document.querySelector('.stats.svelte-1vzkkpc');
        if (statsContainer) {
            injectMinStat(statsContainer);
        }
    }

    // Observadores (con debounce para no saturar mientras se hace scroll).
    // Se añade "characterData" además de "childList": si un precio se
    // actualiza cambiando solo el texto de un nodo ya existente (en vez de
    // añadir/quitar elementos), un observer que solo mira childList no se
    // entera de ese cambio.
    let scanTimeout = null;
    const scanObserver = new MutationObserver(() => {
        clearTimeout(scanTimeout);
        scanTimeout = setTimeout(scanVisiblePanels, 200);
    });
    scanObserver.observe(document.body, { childList: true, subtree: true, characterData: true });

    let injectTimeout = null;
    const injectObserver = new MutationObserver(() => {
        clearTimeout(injectTimeout);
        injectTimeout = setTimeout(tryInject, 100);
    });
    injectObserver.observe(document.body, { childList: true, subtree: true, characterData: true });

    // Poll de refuerzo: no depende de que el observer detecte el mutation
    // "correcto", simplemente revisa los paneles visibles cada pocos ms
    // mientras estén montados. Esto es lo que realmente evita perder juegos
    // al scrollear rápido.
    setInterval(scanVisiblePanels, POLL_INTERVAL_MS);

    // Primer intento al cargar la página
    scanVisiblePanels();
    tryInject();
})();
