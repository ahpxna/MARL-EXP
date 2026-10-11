# Freeze record, TSI evidence chain (written 05/10 10:47 AFTER the runs; agent-B audit finding 2, ledger C-128)

The TSI, TSI-2, SHIFT, GEN, PERF and spider protocols had no launch-time hash record, and the TSI / HYB rows carry no forecaster, fleet or table hash.
This record fixes the CURRENT sha256 of every module and input on those paths. The link to the runs is by file modification time only:
each file below is older than the first run that used it (agent B: CITY_spat_forecast_n4.py 00:50:37 vs the first TSI run 01:08; CITY_n2k.py 07:24:14,
after the spider collection, which logs raw states only, and before the fit at 07:25:30).
A hash recorded inside a row (source_sha256, provider / fleet hashes of R, ADP2 and F1B rows) equals the current source wherever it exists (agent B, checked 05/10 10:5x).

| file | sha256 | modified |
|---|---|---|
| `scripts/CITY_env.py` | `02a297a56a12955d…` | 10/02 23:46:58 |
| `scripts/CITY_eval4.py` | `92195f159407719c…` | 10/04 05:57:59 |
| `scripts/CITY_eval_f1.py` | `3b09b5aa39f42cc9…` | 10/04 19:59:30 |
| `scripts/CITY_eval_f1b.py` | `f3a9a2dcbb77af65…` | 10/04 22:40:09 |
| `scripts/CITY_eval_n4.py` | `00eabd0f471f7772…` | 10/05 00:38:59 |
| `scripts/CITY_spat_forecast.py` | `f0fe94f9a7e76ae3…` | 10/04 16:52:24 |
| `scripts/CITY_spat_forecast_c2.py` | `a4091303e92c770a…` | 10/04 22:36:54 |
| `scripts/CITY_spat_forecast_n2.py` | `c9e5d8c42c99d260…` | 10/05 00:17:19 |
| `scripts/CITY_spat_forecast_n4.py` | `524800ddb0c01a6f…` | 10/05 00:50:37 |
| `scripts/CITY_n2_fit.py` | `a48114b1b0ced67a…` | 10/05 00:15:58 |
| `scripts/CITY_n2_collect.py` | `6e6328f9ba40de65…` | 10/05 00:14:07 |
| `scripts/CITY_n2k.py` | `dd8d255dc263e887…` | 10/05 07:24:14 |
| `scripts/CITY_f1a1_run.py` | `a517bb07ea0e2da3…` | 10/04 21:09:54 |
| `scripts/CITY_xplay2.py` | `4f41f5664ebec111…` | 10/04 03:53:02 |
| `scripts/CITY_q7_cross_version.py` | `a88f724ac9e02c1a…` | 10/02 21:48:27 |
| `scripts/CITY_m4s_tsi_eval.py` | `921c061df362430b…` | 10/05 07:20:52 |
| `scripts/CITY_m4s_f1k_eval.py` | `34d82814491ad12f…` | 10/04 21:35:10 |
| `scripts/CITY_lightk.py` | `e5c63e5752db335e…` | 10/04 05:58:37 |
| `scripts/CITY_spat_forecast_k.py` | `7848a3f3219b83dc…` | 10/04 21:33:24 |
| `scripts/CITY_tsi2_tune.py` | `91fc642530805252…` | 10/05 01:47:26 |
| `scripts/CITY_tsi2_report.py` | `88db4f8b32f12787…` | 10/05 01:47:26 |
| `scripts/CITY_tsi_confirm_report.py` | `48ef5b0ee61cae77…` | 10/05 01:02:49 |
| `scripts/CITY_shift_report.py` | `43489e175163ec7a…` | 10/05 01:50:49 |
| `scripts/CITY_gen_report.py` | `2b5519a85a39ba53…` | 10/05 01:54:59 |
| `scripts/CITY_rho_run.py` | `b541bd460269a6fd…` | 10/05 01:54:59 |
| `scripts/CITY_perf_report.py` | `9388c6908c777a05…` | 10/05 04:54:01 |
| `scripts/CITY_sptsi_tune.py` | `d62f418e8fa848ea…` | 10/05 07:27:17 |
| `scripts/CITY_sptsi_report.py` | `5844f878b28844ad…` | 10/05 07:27:17 |
| `scripts/CITY_wave2_report_v2.py` | `bf1b14ea14e2b0f0…` | 10/04 08:47:08 |
| `scripts/CITY_spatp_report.py` | `b6e5280cc7d52774…` | 10/04 12:38:56 |
| `scripts/CITY_fleet_train_f1b.py` | `7fa25868582bcde4…` | 10/04 22:40:09 |
| `research/city_sim/tsi_20261005/cmodel/c2/n2_k4.pt` | `b058d120587a7968…` | 10/05 01:15:41 |
| `research/city_sim/tsi_20261005/cmodel/c2/n2_k5.pt` | `9fc1a5250734f035…` | 10/05 01:15:41 |
| `research/city_sim/tsi_20261005/cmodel/c2/n2_k6.pt` | `5efd754ee2c27227…` | 10/05 01:15:41 |
| `research/city_sim/tsi_20261005/cmodel/c2/n2_k7.pt` | `c50223e3f8875606…` | 10/05 01:15:41 |
| `research/city_sim/tsi_20261005/cmodel/c2/n2_k8.pt` | `8f75da4e59959a20…` | 10/05 01:16:07 |
| `research/city_sim/f1b_20261004/prep/prov_rlh4_cl.json` | `cc5abd483fd810c2…` | 10/04 23:25:07 |
| `research/city_sim/f1b_20261004/prep/prov_rlh5_cl.json` | `cb9ea865f9c78e60…` | 10/04 23:25:12 |
| `research/city_sim/f1b_20261004/prep/prov_rlh6_cl.json` | `42bc220d4782827e…` | 10/04 23:25:11 |
| `research/city_sim/f1b_20261004/prep/prov_rlh7_cl.json` | `e803b73a44e013ce…` | 10/04 23:25:10 |
| `research/city_sim/f1b_20261004/prep/prov_rlh8_cl.json` | `102b3a9f37ce12bf…` | 10/04 23:25:11 |
| `research/city_sim/m3_lights_20261004/RL-H_t4.pt` | `fb270118b4290fe0…` | 10/04 17:59:10 |
| `research/city_sim/m3_lights_20261004/RL-H_t5.pt` | `05dd8e343fb8be2b…` | 10/04 17:59:11 |
| `research/city_sim/m3_lights_20261004/RL-H_t6.pt` | `84aec1b6d8e3d00b…` | 10/04 17:59:10 |
| `research/city_sim/m3_lights_20261004/RL-H_t7.pt` | `4974f29e2848f584…` | 10/04 17:59:10 |
| `research/city_sim/m3_lights_20261004/RL-H_t8.pt` | `fa94eeff966fc612…` | 10/04 17:59:10 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s113_fleet.pt` | `1ff78f6b85bc4679…` | 10/04 16:24:37 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt` | `e5c238289d5584d1…` | 10/04 16:24:50 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s213_fleet.pt` | `81089d52a031bf4d…` | 10/04 16:16:16 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s313_fleet.pt` | `681c3081f7fdc9a1…` | 10/04 16:24:28 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s413_fleet.pt` | `7b511a2653905005…` | 10/04 16:24:52 |
| `research/city_sim/spat_pilot_20261004/fleets_v11/L11_s513_fleet.pt` | `1a6e48b5e313bc9a…` | 10/04 16:24:49 |
| `research/city_sim/f1b_20261004/train/F1B_s213_t4_fleet.pt` | `fa397493e4bd1f44…` | 10/04 23:49:08 |
| `research/city_sim/f1b_20261004/train/F1B_s313_t5_fleet.pt` | `3ffc4c52908344a1…` | 10/04 23:48:14 |
| `research/city_sim/f1b_20261004/train/F1B_s413_t6_fleet.pt` | `65ba2b6de3f31f3d…` | 10/04 23:48:18 |
| `research/city_sim/f1b_20261004/train/F1B_s513_t7_fleet.pt` | `250a2cdf50282822…` | 10/04 23:48:09 |
| `research/city_sim/sptsi_20261005/model/n2k_sp11.pt` | `1a7942b6bd9a3d8a…` | 10/05 07:25:30 |
| `research/city_sim/sptsi_20261005/model/n2k_sp111.pt` | `1a40042448244c47…` | 10/05 07:25:30 |
| `research/city_sim/m4_20261004/spider/s3b/prov/fkcl_rlk11.json` | `2cc5c6536e5f00ab…` | 10/04 22:11:52 |
| `research/city_sim/m4_20261004/spider/s3b/prov/fkcl_rlk111.json` | `08dcd916056fcc4d…` | 10/04 22:11:54 |
| `research/city_sim/m4_20261004/spider/RLK_sp11.pt` | `f987cec9f9d6f1d3…` | 10/04 20:32:18 |
| `research/city_sim/m4_20261004/spider/RLK_sp111.pt` | `9ec2adf44db3fc1f…` | 10/04 20:32:16 |
| `research/city_sim/tsi2_20261005/tune/choice.json` | `447d508c7db5114d…` | 10/05 01:58:10 |
| `research/city_sim/sptsi_20261005/tune/choice.json` | `6d5f487dd568c6dc…` | 10/05 07:26:34 |
| `research/city_sim/sptsi_20261005/tune2/choice.json` | `726ddd76956ed566…` | 10/05 07:29:25 |
