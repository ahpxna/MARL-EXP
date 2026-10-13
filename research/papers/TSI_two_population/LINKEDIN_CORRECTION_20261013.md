# LinkedIn correction for the TSI poster (draft, 13/10/2026; post with TSI_poster_v5.pdf)

Update to the poster I shared last week. I re-checked every number against our pre-registered results and corrected a few statements (v5 attached):

• On RESCO's MPLight state, TSI-G cuts the cooperating cars' extra delay from 16.0 to 0.5 s/veh, but that is just above our pre-registered +0.5 s limit, so it does not count as a pass. It does repair sumo-rl's default and RESCO's IDQN/IPPO state.
• sumo-rl's and RESCO's default states do see moving cars (density, approach counts, speeds). The problem is their stop-based queue, waiting-time and pressure features: learned lights trained on them serve gliding cars later.
• The 5–10% fuel savings are under the HBEFA4 model with SUMO's default drivers. Under PHEMlight5 they are 3–6%, and against drivers matched to real NGSIM trajectories the fleet saves about 1%. The robust result is the time effect.
• The default repair tolerates a 1-s SPaT delay and 20–50% message loss; the transfers to other networks used recalibration.

Thanks to everyone who looked at it. Corrections like these are part of doing the research properly.
