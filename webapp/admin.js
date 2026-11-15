/* Панель продавца: подгружается только для ADMIN_ID. Использует api/esc/toast/rub/tg из index.html */
(function () {
  const st = { tab: 'orders', filter: 'active', orders: null, products: null, q: '', days: 7, stats: null, timer: null };
  let root = null;
  const PAY = { unpaid: 'ждём оплату', claimed: 'клиент сообщил об оплате', paid: 'оплачено' };

  const style = document.createElement('style');
  style.textContent = `.arow{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}
  .arow button{flex:1 1 auto;padding:10px 12px;border-radius:11px;background:var(--bg);font-weight:600;font-size:13.5px}
  .arow .pr{background:var(--btn);color:var(--btn-fg)}.arow .dg{color:var(--red)}
  .kpis{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:12px 0}
  .kpi{background:var(--card);border-radius:14px;padding:11px 13px}.kpi b{display:block;font-size:19px}.kpi span{font-size:12px;color:var(--hint)}
  .fld{display:block;margin:10px 0 0;font-size:12.5px;color:var(--hint)}
  .fld input,.fld textarea{display:block;width:100%;margin-top:4px;padding:10px 12px;border-radius:11px;border:1px solid var(--line);background:var(--card);font:inherit;color:var(--fg);outline:none}
  .two{display:grid;grid-template-columns:1fr 1fr;gap:8px}
  .bar-row{display:flex;align-items:center;gap:8px;font-size:13px;margin:6px 0}.bar-row i{display:block;height:9px;border-radius:5px;background:var(--btn)}
  .dim{opacity:.5}`;
  document.head.appendChild(style);

  window.openAdmin = function () {
    if (root) return;
    root = document.createElement('div'); root.className = 'full'; root.style.zIndex = 18;
    document.body.appendChild(root);
    root.addEventListener('click', onClick);
    st.timer = setInterval(() => { if (st.tab === 'orders' && !document.querySelector('.sheet-bg')) loadOrders(); }, 15000);
    show(); loadOrders();
  };
  function close() { clearInterval(st.timer); root.remove(); root = null; }
  const hapOk = () => { try { tg.HapticFeedback.notificationOccurred('success'); } catch (e) {} };

  function ask(title, ph, val) {
    return new Promise(res => {
      const d = document.createElement('div'); d.className = 'sheet-bg'; d.style.zIndex = 40;
      d.innerHTML = `<div class="sheet"><h2>${esc(title)}</h2><input class="search" id="ai" placeholder="${esc(ph)}" value="${esc(val || '')}" maxlength="60">
        <button class="cta" data-ok>Готово</button><button class="ghost" data-no>Отмена</button></div>`;
      d.onclick = e => { const t = e.target; if (t === d || t.dataset.no !== undefined) { d.remove(); res(null); } else if (t.dataset.ok !== undefined) { const v = d.querySelector('#ai').value.trim(); d.remove(); res(v || null); } };
      document.body.appendChild(d); d.querySelector('#ai').focus();
    });
  }
  const sure = msg => new Promise(res => tg && tg.showConfirm ? tg.showConfirm(msg, res) : res(confirm(msg)));

  function show() {
    const tabs = [['orders', 'Заказы'], ['products', 'Товары'], ['stats', 'Статистика']];
    root.innerHTML = `<div class="in"><div class="top"><h1>⚙️ Панель</h1><button class="chip" data-x>✕ Закрыть</button></div>
      <div class="seg" style="margin:10px 0">${tabs.map(([k, v]) => `<button data-t="${k}" class="${st.tab === k ? 'on' : ''}">${v}</button>`).join('')}</div>
      <div id="body"></div></div>`;
    draw();
  }
  function draw() {
    const b = root.querySelector('#body'); if (!b) return;
    b.innerHTML = st.tab === 'orders' ? ordersHtml() : st.tab === 'products' ? productsHtml() : statsHtml();
  }

  /* ── Заказы ── */
  async function loadOrders() {
    try { st.orders = (await api('admin/orders', { filter: st.filter })).orders || []; } catch (e) { st.orders = st.orders || []; }
    if (root && st.tab === 'orders') draw();
  }
  function ordersHtml() {
    let h = `<div class="chips"><button class="chip ${st.filter === 'active' ? 'on' : ''}" data-f="active">Активные</button>
      <button class="chip ${st.filter === 'all' ? 'on' : ''}" data-f="all">Все</button><button class="chip" data-reload>⟳ Обновить</button></div>`;
    if (st.orders === null) return h + '<div class="empty">Загрузка…</div>';
    if (!st.orders.length) return h + '<div class="empty">Заказов нет</div>';
    return h + st.orders.map(o => {
      const act = o.status === 'new' || o.status === 'ready', unpaid = o.payment === 'transfer' && o.pay_status !== 'paid';
      const btn = [];
      if (act && unpaid) { btn.push(`<button class="pr" data-act="paid" data-id="${o.id}">💸 Оплата получена</button>`);
        if (o.pay_status === 'claimed') btn.push(`<button data-act="nopay" data-id="${o.id}">🚫 Оплаты нет</button>`); }
      if (act && o.status === 'new') btn.push(`<button class="pr" data-act="room" data-id="${o.id}">📍 Собран</button>`);
      if (act && o.status === 'ready') { btn.push(`<button class="pr" data-act="done" data-id="${o.id}">✅ Выдан</button>`, `<button data-act="room" data-id="${o.id}" data-room="${esc(o.room)}">📍 Комната</button>`); }
      if (act) btn.push(`<button class="dg" data-act="cancel" data-id="${o.id}">❌ Отменить</button>`);
      return `<div class="order"><div class="h"><span>#${o.id} · ${esc(o.who || 'клиент')}${o.username ? ' @' + esc(o.username) : ''}</span><span>${rub(o.total)}</span></div>
        <div>${o.icon} ${esc(o.label)} · ${o.payment === 'cash' ? '💵 наличные' : '💸 перевод'} (${PAY[o.pay_status] || o.pay_status})</div>
        <div class="i">${o.items.map(i => esc(i.name) + ' ×' + i.qty).join(', ')}</div>
        <div class="i">${esc(o.date)}${o.room ? ' · 📍 ' + esc(o.room) : ''}${o.promo ? ' · 🏷 ' + esc(o.promo) + ' −' + o.discount + ' ₽' : ''}${o.fee ? ' · доплата +' + o.fee + ' ₽' : ''}</div>
        ${btn.length ? `<div class="arow">${btn.join('')}</div>` : ''}</div>`;
    }).join('');
  }
  async function orderAct(id, action, room) {
    const r = await api('admin/order_action', { id, action, room });
    if (r.error) toast(r.error); else { hapOk(); toast(r.refund ? `Отменён. Верните клиенту ${r.refund} ₽` : 'Готово ✅'); }
    loadOrders();
  }

  /* ── Товары ── */
  async function loadProducts() {
    try { st.products = (await api('admin/products')).products || []; } catch (e) { st.products = st.products || []; }
    if (root && st.tab === 'products') draw();
  }
  function productsHtml() {
    if (st.products === null) { loadProducts(); return '<div class="empty">Загрузка…</div>'; }
    const q = st.q.toLowerCase();
    const list = st.products.filter(p => !q || (p.name + ' ' + p.sku).toLowerCase().includes(q));
    return `<button class="cta" data-new style="margin:0 0 10px">+ Добавить товар</button>
      <input class="search" id="pq" placeholder="🔎 Поиск" value="${esc(st.q)}">` +
      list.map(p => `<div class="row ${p.active ? '' : 'dim'}" data-edit="${p.id}" style="cursor:pointer"><div class="n">${esc(p.name)}
        <small>${esc(p.sku)} · ${p.sale_price ? '🔥 ' + rub(p.sale_price) + ' (было ' + rub(p.price) + ')' : rub(p.price)} · остаток ${p.stock}${p.active ? '' : ' · скрыт'}</small></div><span style="color:var(--hint)">›</span></div>`).join('');
  }
  function editSheet(p) {
    const n = !p; p = p || { name: '', price: '', sale_price: '', cost: '', stock: 0, cat: '', desc: '', active: true };
    const d = document.createElement('div'); d.className = 'sheet-bg'; d.style.zIndex = 40;
    const f = (k, l, v, t) => `<label class="fld">${l}<input data-k="${k}" ${t || ''} value="${esc(v ?? '')}"></label>`;
    d.innerHTML = `<div class="sheet"><h2>${n ? 'Новый товар' : 'Товар ' + esc(p.sku)}</h2>
      ${f('name', 'Название', p.name, 'maxlength=80')}
      <div class="two">${f('price', 'Цена, ₽', p.price, 'inputmode=numeric')}${f('sale_price', 'Акционная цена', p.sale_price || '', 'inputmode=numeric')}</div>
      <div class="two">${f('cost', 'Закупка, ₽', p.cost ?? '', 'inputmode=decimal')}${f('stock', 'Остаток, шт.', p.stock, 'inputmode=numeric')}</div>
      ${f('category', 'Категория', p.cat, 'maxlength=30')}
      <label class="fld">Описание<textarea data-k="description" rows="3" maxlength="600">${esc(p.desc)}</textarea></label>
      <label class="fld" style="display:flex;gap:8px;align-items:center"><input type="checkbox" data-k="active" style="width:auto;margin:0" ${p.active ? 'checked' : ''}> Показывать в каталоге</label>
      ${n ? '<p class="status">Фото можно добавить после сохранения.</p>' : `<div class="arow"><button data-photo>📷 ${p.photo ? 'Заменить фото' : 'Загрузить фото'}</button></div><input type="file" accept="image/*" id="pf" hidden>`}
      <button class="cta" data-save style="margin-top:14px">Сохранить</button>
      ${n ? '' : '<button class="ghost dg" data-del style="color:var(--red)">🗑 Удалить товар</button>'}
      <button class="ghost" data-no>Закрыть</button></div>`;
    d.onclick = async e => {
      const t = e.target;
      if (t === d || t.dataset.no !== undefined) return d.remove();
      if (t.dataset.photo !== undefined) return d.querySelector('#pf').click();
      if (t.dataset.save !== undefined) {
        const body = { id: p.id }; d.querySelectorAll('[data-k]').forEach(i => body[i.dataset.k] = i.type === 'checkbox' ? i.checked : i.value.trim());
        const r = await api('admin/product_save', body);
        if (r.error) return toast(r.error);
        hapOk(); toast('Сохранено ✅'); d.remove(); loadProducts(); S && load();
      }
      if (t.dataset.del !== undefined && await sure(`Удалить «${p.name}» навсегда? Артикулы пересортируются.`)) {
        const r = await api('admin/product_delete', { id: p.id }); if (r.error) return toast(r.error);
        toast('Удалено 🗑'); d.remove(); loadProducts(); load();
      }
    };
    const pf = d.querySelector('#pf');
    if (pf) pf.onchange = async () => {
      const file = pf.files[0]; if (!file) return; toast('Загружаем…');
      try {
        const bmp = await createImageBitmap(file), k = Math.min(1, 1000 / Math.max(bmp.width, bmp.height));
        const cv = document.createElement('canvas'); cv.width = Math.round(bmp.width * k); cv.height = Math.round(bmp.height * k);
        cv.getContext('2d').drawImage(bmp, 0, 0, cv.width, cv.height);
        const blob = await new Promise(r => cv.toBlob(r, 'image/jpeg', 0.85));
        const fd = new FormData(); fd.append('id', p.id); fd.append('file', blob, 'p.jpg');
        const r = await (await fetch('/api/admin/photo', { method: 'POST', headers: { 'X-Init-Data': tg.initData }, body: fd })).json();
        if (r.ok) { hapOk(); toast('Фото сохранено ✅'); loadProducts(); load(); } else toast(r.error || 'Не получилось');
      } catch (e) { toast('Не удалось загрузить фото'); }
    };
    document.body.appendChild(d);
  }

  /* ── Статистика ── */
  async function loadStats() {
    try { st.stats = await api('admin/stats', { days: st.days }); } catch (e) { st.stats = { series: [], kpi: {}, top: [], low: [] }; }
    if (root && st.tab === 'stats') draw();
  }
  function chart(sr) {
    const W = 320, H = 150, pad = 18, max = Math.max(1, ...sr.map(x => Math.max(x.rev, x.profit)));
    const bw = (W - 8) / sr.length, y = v => H - pad - (v / max) * (H - pad - 12);
    let g = '';
    sr.forEach((x, i) => {
      const cx = 4 + i * bw, w = Math.max(1, bw * 0.7);
      g += `<rect x="${cx}" y="${y(x.rev)}" width="${w}" height="${H - pad - y(x.rev)}" rx="1.5" fill="var(--btn)"/>`;
      if (x.profit > 0) g += `<rect x="${cx}" y="${y(x.profit)}" width="${w}" height="${H - pad - y(x.profit)}" rx="1.5" fill="var(--green)" opacity=".85"/>`;
      if (sr.length <= 10 || i % Math.ceil(sr.length / 6) === 0) g += `<text x="${cx + w / 2}" y="${H - 4}" text-anchor="middle" font-size="9" fill="var(--hint)">${x.d}</text>`;
    });
    return `<svg viewBox="0 0 ${W} ${H}" width="100%"><text x="2" y="10" font-size="9" fill="var(--hint)">макс ${rub(max)}</text>${g}</svg>
      <div class="status"><span style="color:var(--btn)">■</span> выручка &nbsp; <span style="color:var(--green)">■</span> прибыль</div>`;
  }
  function statsHtml() {
    if (!st.stats) { loadStats(); return '<div class="empty">Загрузка…</div>'; }
    const k = st.stats.kpi, top = st.stats.top, mx = Math.max(1, ...top.map(t => t.qty));
    return `<div class="chips">${[7, 30, 90].map(n => `<button class="chip ${st.days === n ? 'on' : ''}" data-d="${n}">${n} дн.</button>`).join('')}</div>
      <div class="kpis"><div class="kpi"><b>${rub(k.revenue || 0)}</b><span>Выручка</span></div><div class="kpi"><b>${rub(k.profit || 0)}</b><span>Прибыль</span></div>
      <div class="kpi"><b>${k.done || 0}</b><span>Выдано заказов</span></div><div class="kpi"><b>${rub(k.avg || 0)}</b><span>Средний чек</span></div>
      <div class="kpi"><b>${k.active || 0}</b><span>В работе (${rub(k.pending || 0)})</span></div><div class="kpi"><b>${k.repeat || 0} из ${k.buyers || 0}</b><span>Покупателей повторно</span></div></div>
      <div class="sum">${chart(st.stats.series)}</div>
      <h3 style="margin:14px 0 4px">🏆 Топ товаров</h3>${top.length ? top.map(t => `<div class="bar-row"><span style="flex:0 0 42%">${esc(t.name)}</span><i style="width:${Math.max(4, t.qty / mx * 40)}%"></i><b>${t.qty}</b></div>`).join('') : '<div class="status">Пока нет продаж</div>'}
      ${st.stats.low.length ? `<h3 style="margin:14px 0 4px">⚠️ Заканчивается</h3>${st.stats.low.map(l => `<div class="bar-row"><span style="flex:1">${esc(l.name)}</span><b>${l.stock} шт.</b></div>`).join('')}` : ''}
      <div class="status">В выручке и прибыли — только выданные заказы.</div>`;
  }

  /* ── События ── */
  async function onClick(e) {
    const t = e.target.closest('button,[data-edit]'); if (!t) return; const ds = t.dataset;
    if (ds.x !== undefined) return close();
    if (ds.t) { st.tab = ds.t; show(); if (ds.t === 'orders') loadOrders(); if (ds.t === 'products') loadProducts(); if (ds.t === 'stats') loadStats(); }
    else if (ds.f) { st.filter = ds.f; st.orders = null; draw(); loadOrders(); }
    else if (ds.reload !== undefined) loadOrders();
    else if (ds.d) { st.days = +ds.d; st.stats = null; draw(); loadStats(); }
    else if (ds.new !== undefined) editSheet(null);
    else if (ds.edit) editSheet(st.products.find(p => p.id === +ds.edit));
    else if (ds.act) {
      const id = +ds.id;
      if (ds.act === 'room') { const room = await ask('📍 Комната выдачи', 'например 412', ds.room); if (room) orderAct(id, 'room', room); }
      else if (ds.act === 'cancel') { if (await sure(`Отменить заказ #${id}? Товар вернётся на склад.`)) orderAct(id, 'cancel'); }
      else orderAct(id, ds.act);
    }
  }
  root = null;
  document.addEventListener('input', e => { if (e.target.id === 'pq') { st.q = e.target.value; const b = root && root.querySelector('#body'); if (b) { b.innerHTML = productsHtml(); const i = b.querySelector('#pq'); i.focus(); i.setSelectionRange(st.q.length, st.q.length); } } });
})();
