#!/usr/bin/env python3
"""TSI poster v5 (13/10/2026): v4 corrected after the review research/papers/audits/POSTER_TSI_V4_REVIEW_20261013.md.
Same source slide, layout engine and two-pass build as v4 (scripts/POSTER_tsi_v4.py, imported unchanged); only the text is replaced (TEXT
entries below override v4's), Fig. 3 is fig3_bars_v5.png (axis 'extra delay', group 'stop-based inputs', the +0.5 limit drawn), and after
each pass the output is post-processed:
  - the queue-model equation is re-rendered in the ink of the other equations (it was dark red) and its symbols are defined in the text;
  - the stray asterisk before the NSF statement is removed (no author carries one);
  - the document title / author / subject are set (the file had no core properties).
Corrections (review IDs): A1 MPLight not repaired by the registered rule; A2 sumo-rl / RESCO drq see moving cars through density / approach /
speed, only their queue, wait and pressure counts are stop-based; A3 the cities' rule is about stop-thresholded inputs; A4 transfer used
recalibrations, the default's robustness is delay / loss / noise (80% detection missed the limit); A5 fuel ranges under both models;
A6 axis = delay; B1 limitations name the driver-model result (W17); B2 Salt Lake is against human drivers and the upgrade did not break the
fleet; B3 the 3.85% is HBEFA4; C1-C4, C6, C9 wording.
Usage: POSTER_tsi_v5.py <in pptx> <fig3 png> <out pptx> [--heights JSON]  |  POSTER_tsi_v5.py measure <pdf> <pos json> <out heights json>"""
import hashlib, io, json, sys
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pptx import Presentation
from pptx.util import Emu
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.POSTER_tsi_v4 as V4  # noqa: E402

NEW_TEXT = {
    4: ("Fig. 1.  The upgrade erases a learned fleet's benefit.",
        ' Against its own base driver the fleet saves fuel under fixed-time signals (blue). Under a learned signal without timing it is its base driver (grey, zero by construction); with the old timing served as SPaT it loses fuel and time (orange). R9, R10: learned fleets; rule: a GLOSA rule (spider network).'),
    7: ('Why.',
        ' Learned lights usually count a car as waiting only once it has stopped (below 0.1 m/s), the default in sumo-rl [10] and RESCO [11]. A gliding car never enters these queue, waiting or pressure counts, so the light serves it later. We keep both AIs frozen and change only what the fleet is told and what the light senses.'),
    16: ('Fleet side.',
         " The old timing is replaced by a hybrid provider: exact when the timing is determined (a yellow whose next green serves the link), otherwise a state-conditioned quantile forecaster fitted to eight logged episodes of the deployed signal, its pinball loss weighted by the fleet's query count Q:"),
    23: ('Why both sides.',
         " In a threshold-queue model where vehicles arrive at rate λ, a fleet share ρ glides, and the signal serves once its input, weighting a glider by A, reaches θ, a forecast learned without the fleet errs by"),
    30: ('Fig. 3.  Who pays for the forecast, and the repair.',
         " (A) Extra delay of the fleet's cars vs no SPaT (5 signals × 4 fleets × 20 fresh seeds; 95% intervals). Blue: TSI on RL-H, TSI-G elsewhere; it removes the delay except +0.5 s/veh on MPLight, just above the limit. Without a stop-based input no repair is needed. (B) Fleet fuel saved."),
    49: ('The repair works.',
         " Registered confirmation: TSI cut fleet fuel by 3.85% (HBEFA4; 95% CI 3.26–4.43), all limits met. Its default, fixed in advance, saves 5.6% (HBEFA4) and 3.3% (PHEMlight5) on new signals and fleets; with a per-signal quantile it tolerates a 1-s delay, 20–50% message loss and speed noise. Recalibrated, it passed on a second network and a two-lane build of a third; our DC-Ada and FoRL ports miss the limits."),
    31: ('We pinpoint the cause: the stop threshold.',
         " Trained by the same recipe, signals with no stop-thresholded input (speed groups, queue positions, RESCO's wave) need no repair: the forecast alone meets every limit and their greens do not lengthen, also with a delay reward or with scale constants halved or doubled."),
    33: ('TSI-G removes over 95% of the harm, no retraining.',
         " Forecast alone, the fleet's cars lose 5.4 s/veh under sumo-rl's default, 2.6 under RESCO's IDQN / IPPO state and 16.0 under MPLight; with TSI-G, −0.2, −0.2 (limits met) and 0.5 (just above our limit), saving 5–10% fuel (HBEFA4; 3–6% PHEMlight5)."),
    36: ('Fig. 4.  Mechanism.',
         " Under the service the learned signal holds its greens longer (A); the fleet's extra time grows with that lengthening (B, first TSI attempt); on a replayed schedule exact timing saves both fuel and time (C)."),
    37: ('A prediction made before the run held.',
         " Varaiya's MaxPressure counts vehicles at every speed, so the model says the forecast alone should suffice: registered in advance, the fleet-side service alone met every limit (−2.68%) and the greens did not lengthen."),
    'field': ('Checked against field data.',
              ' On real adaptive signals in Hamburg the forecaster holds its 0.1 quantile on held-out days; measured fuel (VED) supports PHEMlight5; on recorded Salt Lake City demand the fleet saves about 10% against human drivers, and the upgrade did not break it.'),
    41: ('',
         "Simulation with SUMO's default drivers: against drivers matched to NGSIM trajectories the fleet saves about 1% fuel (HBEFA4), none detectable under PHEMlight5, so the robust result is the time effect. A road pilot is next. Each forecaster uses its signal's own logs; TSI-G needs V2X to know the SPaT cars."),
    44: ('Bottom line.',
         ' AI lights and AI cars run by different owners depend on each other, and upgrading one can quietly break the other. The break runs through what the light counts; sensing each SPaT car as the human it replaces removes nearly all of the harm without retraining either AI.'),
    45: ('For cities and carmakers:',
         " before cars use a learned light's SPaT, check what it counts: any stop-based input (queue, wait, queued pressure) needs TSI or TSI-G, even beside speed or density; without one, the forecast alone works."),
}
V4.TEXT.update(NEW_TEXT)
V4.REFS_ADD = (' [10] L. N. Alegre, “SUMO-RL,” GitHub, 2019. [11] J. Ault, G. Sharon, “Reinforcement learning benchmarks for traffic signal control,” '
               'NeurIPS Datasets and Benchmarks, 2021.')
QUEUE_TEX = r'T - T_0 \;=\; T_0\,\frac{\rho\,(1-A)}{1-\rho\,(1-A)},\qquad T_0=\frac{\theta}{\lambda}'
INK = '#161213'                                   # scripts/POSTER_equations.py ink
SRC_EQ_SHA = None                                 # sha1 of the dark-red queue equation in the source slide (shape 24), set in main


def render_eq(tex):
    matplotlib.rcParams['mathtext.fontset'] = 'cm'
    fig = plt.figure(figsize=(0.01, 0.01)); fig.text(0, 0, f'${tex}$', fontsize=30, color=INK); buf = io.BytesIO()
    fig.savefig(buf, dpi=600, bbox_inches='tight', pad_inches=0.06, transparent=True); plt.close(fig); return buf.getvalue()


def post(out, src_eq_sha):
    prs = Presentation(out); sl = prs.slides[0]; done = dict(eq=False, star=False)
    for s in sl.shapes:
        if s.shape_type == 13 and hashlib.sha1(s.image.blob).hexdigest() == src_eq_sha:
            new = render_eq(QUEUE_TEX); rid = s._element.blipFill.blip.rEmbed; part = s.part.related_part(rid); part._blob = new
            from PIL import Image
            wpx, hpx = Image.open(io.BytesIO(new)).size; cx = s.left + s.width / 2; h = s.height; w = int(h * wpx / hpx)
            s.width = Emu(w); s.left = Emu(int(cx - w / 2)); done['eq'] = True
        if s.has_text_frame:
            for p in s.text_frame.paragraphs:
                if p.runs and p.runs[0].text.startswith('*This material'):
                    p.runs[0].text = p.runs[0].text[1:]; done['star'] = True
    cp = prs.core_properties
    cp.title = 'Staged Upgrades of Two Learned Populations: A Two-Sided Interface That Recovers a Learned Fleet\'s Benefit When Its Signals Are Upgraded'
    cp.author = 'Vu Phan An Nguyen'; cp.subject = 'Poster v5 (13/10/2026), Rider University; mentor Dr. Jay Zhengping Luo'
    cp.keywords = 'traffic signal control; eco-driving; SPaT; reinforcement learning; TSI; TSI-G'; cp.last_modified_by = 'Vu Phan An Nguyen'
    prs.save(out); print('post-processed', out, done)
    assert done['eq'] and done['star'], f'post-processing incomplete: {done}'


if __name__ == '__main__':
    if sys.argv[1] == 'measure':
        V4.measure_pdf(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        src = sys.argv[1]; S = list(Presentation(src).slides[0].shapes); eq_sha = hashlib.sha1(S[24].image.blob).hexdigest()
        hj = json.loads(Path(sys.argv[sys.argv.index('--heights') + 1]).read_text()) if '--heights' in sys.argv else None
        V4.main(src, sys.argv[2], sys.argv[3], hj); post(sys.argv[3], eq_sha)
