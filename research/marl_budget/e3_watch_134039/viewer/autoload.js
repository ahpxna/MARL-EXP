const RUNS = ["scratch_s3", "mp2"];
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
})();
