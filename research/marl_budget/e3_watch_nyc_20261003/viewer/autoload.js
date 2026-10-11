const RUNS = ["teacher", "mp2"];
// autoload.js (MARL_e3_watch_episode.py): fetch the run's files, put them in the upload inputs, press Start.
(async function () {
  const run = new URLSearchParams(location.search).get('run') || RUNS[0];
  const put = async (id, url, name) => {
    const r = await fetch(url); if (!r.ok) return false;
    const dt = new DataTransfer(); dt.items.add(new File([await r.blob()], name));
    const el = document.getElementById(id); el.files = dt.files; el.dispatchEvent(new Event('change')); return true;
  };
  await put('roadnet-file', run + '/replay_roadnet.json', 'replay_roadnet.json');
  await put('replay-file', run + '/replay.txt', 'replay.txt');
  await put('chart-file', run + '/chart.txt', 'chart.txt');
  const nav = document.createElement('div'); nav.style = 'position:fixed;top:4px;right:8px;z-index:9;font:13px sans-serif';
  nav.innerHTML = 'run: ' + RUNS.map(x => x === run ? '<b>' + x + '</b>' : '<a href="?run=' + x + '">' + x + '</a>').join(' | ');
  document.body.appendChild(nav);
  document.getElementById('start-btn').click();
  // legend: Chartist colours its series a, b, c, ... in this order (chartist.min.css defaults); CityFlow's page has none
  const COLORS = ['#d70206', '#f05b4f', '#f4c63d', '#d17905', '#453d3f', '#59922b', '#0544d3', '#6b0392', '#f05b4f', '#dda458'];
  const legend = 'waiting vehicles per second (one line per run; the cars shown are <b>' + run + '</b>): ' +
    RUNS.map((x, i) => '<span style="color:' + COLORS[i % COLORS.length] + ';font-weight:600;white-space:nowrap">&#9632; ' + x + '</span>').join(' &nbsp; ');
  const fix = () => { const t = document.getElementById('chart-title'); if (t && !t.innerHTML.includes('&#9632;') && !t.innerHTML.includes('■')) t.innerHTML = legend; };
  for (let k = 1; k <= 20; k++) setTimeout(fix, 500 * k);
})();
