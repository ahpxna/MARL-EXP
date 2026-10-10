#!/usr/bin/env python3
"""Movement-specific SPaT feature (04/10/2026; user audit CITY_B6_FINAL_AND_SPAT_AUDIT §3.2: getNextSwitch - t is NOT the time-to-green of
the vehicle's movement).  For a vehicle whose next signal is (tid, link) = getNextTLS(v)[0][:2]:
  spat(tid, link) -> dict(ttg, ttr, valid, source)
    ttg  seconds until the vehicle's own link (state[link]) next shows green ('G' or 'g'); 0 if green now
    ttr  seconds until that link next leaves green (yellow onset); 0 if not green now
    valid / source  'program' = derived from a STATIC program (exact by construction if the light follows it); for any light whose
         current program is not static (actuated, or a phase held by setPhaseDuration, e.g. LightRL's 1e5), valid = False and the
         values are 0: a causal forecast for such lights must be designed and validated separately (not this function).
Times are 'the first simulation time at which the observed state shows the event' for this evaluator at dt = 1 s, verified by
CITY_spat_trace_check.py.  Scope: static programs that no controller overrides (FT); a static program whose phases or durations are
changed by a controller is NOT covered."""
import scripts.CITY_env as CE

HELD = 1e4      # a remaining phase time above this is treated as a hold (LightRL sets 1e5), not a plan
OBS = 1.0       # convention of THIS evaluator at step length 1 s (not a general SUMO rule): the new link state is first OBSERVED one step
                # after getNextSwitch (trace check: 39 522 / 39 522 at +1 s before the convention)
ALWAYS = 999.0  # ttr reported for a link that is green in every phase of the program


def spat(tid, link):
    ls = CE.ls; t = ls.simulation.getTime()
    lg = next(l for l in ls.trafficlight.getAllProgramLogics(tid) if l.programID == ls.trafficlight.getProgram(tid))
    rem = ls.trafficlight.getNextSwitch(tid) - t
    if lg.type != 0 or rem > HELD:
        return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    ph = lg.phases; k = ls.trafficlight.getPhase(tid); n = len(ph)
    green = lambda j: ph[j].state[link] in 'Gg'
    if green(k):
        acc, j = rem, (k + 1) % n
        for _ in range(n - 1):                                     # bounded: an always-green link has no end of green
            if not green(j):
                return dict(ttg=0.0, ttr=float(acc) + OBS, valid=True, source='program')
            acc += ph[j].duration; j = (j + 1) % n
        return dict(ttg=0.0, ttr=ALWAYS, valid=True, source='always-green')
    acc, j = rem, (k + 1) % n
    for _ in range(n):
        if green(j):
            return dict(ttg=float(acc) + OBS, ttr=0.0, valid=True, source='program')
        acc += ph[j].duration; j = (j + 1) % n
    return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
