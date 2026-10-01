# E3 results census (every COMPLETE evaluation since 29/09 18:00; read-only)

effect = paired waiting ratio − 1 vs the same-seed zero-byte student on the same episodes (negative = better); 95 % traffic-seed bootstrap.  "—" = no same-seed Z on the same episodes (not paired).


## e3_bytebudget_panel_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| raw_set_full_s0 | set_full_s0 | full | iid | None | seed2101..seed2164 | 128 | 1176 | 5850 | -2.72 [-3.69, -1.74] | PASS |  |
| raw_set_full_s1 | set_full_s1 | full | iid | None | seed2101..seed2164 | 128 | 1133 | 5850 | -3.62 [-4.43, -2.77] | PASS |  |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2101..seed2164 | 128 | 1208 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2101..seed2164 | 128 | 1176 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2101..seed2164 | 128 | 1528 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2101..seed2164 | 128 | 1259 | 0 | +4.16 [+3.08, +5.21] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2101..seed2164 | 128 | 1252 | 0 | +6.45 [+5.34, +7.64] | PASS |  |
| var_set_full_s0 | set_full_s0 | prefix | iid | None | seed2101..seed2164 | 128 | 1173 | 5850 | -2.94 [-3.90, -2.02] | PASS |  |
| var_set_full_s1 | set_full_s1 | prefix | iid | None | seed2101..seed2164 | 128 | 1133 | 5850 | -3.69 [-4.48, -2.90] | PASS |  |

## e3_codesign_eval_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bb_set_full_s1 | set_full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1132 | 5850 | -4.47 [-5.33, -3.58] | PASS |  |
| bb_set_full_s2 | set_full_s2 | prefix | iid | None | seed901..seed964 | 128 | 1162 | 5850 | -4.47 [-5.31, -3.64] | PASS |  |
| bb_set_full_s3 | set_full_s3 | prefix | iid | None | seed901..seed964 | 128 | 1184 | 5850 | -2.52 [-3.36, -1.62] | PASS |  |
| bb_set_full_s4 | set_full_s4 | prefix | iid | None | seed901..seed964 | 128 | 1173 | 5850 | -3.05 [-3.88, -2.27] | PASS |  |
| bb_set_full_s5 | set_full_s5 | prefix | iid | None | seed901..seed964 | 128 | 1225 | 5850 | +0.62 [-0.27, +1.55] | PASS |  |
| bb_set_full_s6 | set_full_s6 | prefix | iid | None | seed901..seed964 | 128 | 1229 | 5850 | -0.71 [-1.44, +0.04] | PASS |  |
| bb_set_full_s7 | set_full_s7 | prefix | iid | None | seed901..seed964 | 128 | 1119 | 5850 | -3.21 [-3.88, -2.49] | PASS |  |
| bb_set_full_s8 | set_full_s8 | prefix | iid | None | seed901..seed964 | 128 | 1258 | 5850 | -1.04 [-1.87, -0.20] | PASS |  |
| bb_set_full_s9 | set_full_s9 | prefix | iid | None | seed901..seed964 | 128 | 1230 | 5850 | -0.21 [-0.97, +0.55] | PASS |  |
| cap6_s0 | cap6_s0 | cap6 | None | None | seed901..seed964 | 128 | 1324 | 3883 | +8.68 [+7.52, +9.95] | PASS |  |
| cap6_s0 | cap6_s0 | prefix | None | None | seed901..seed964 | 128 | 1383 | 4904 | +13.51 [+12.18, +14.78] | PASS |  |
| d3b_flatfull_freshonly | full_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1343 | 2600 | +10.22 [+8.99, +11.48] | PASS |  |
| d3b_flatfull_freshonly | full_s1 | cap4 | iid | None | seed901..seed964 | 128 | 1316 | 2600 | +11.05 [+9.94, +12.12] | PASS |  |
| d3b_flatfull_freshonly | full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1347 | 4906 | +10.59 [+9.51, +11.78] | PASS |  |
| d3b_flatfull_freshonly | full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1310 | 4904 | +10.59 [+9.50, +11.65] | PASS |  |
| d3b_setstale_freshonly | set_prefix_s0 | prefix | iid | None | seed901..seed964 | 128 | 1305 | 4907 | +7.12 [+6.13, +8.09] | PASS |  |
| d3b_setstale_freshonly | set_rxq_s0 | prefix | iid | None | seed901..seed964 | 128 | 1278 | 4901 | +4.93 [+3.90, +6.00] | PASS |  |
| d3w_setfull_freshonly | set_full_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1215 | 2599 | -0.28 [-1.06, +0.55] | PASS |  |
| d3w_setfull_freshonly | set_full_s0 | cap6 | iid | None | seed901..seed964 | 128 | 1220 | 3884 | +0.13 [-0.67, +0.93] | PASS |  |
| d3w_setfull_freshonly | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1217 | 4907 | -0.06 [-0.99, +0.89] | PASS |  |
| d3w_setfull_high | set_full_s0 | full | high | None | seed901..seed964 | 128 | 1185 | 5850 | -2.74 [-3.63, -1.86] | PASS |  |
| d3w_setfull_high | set_full_s0 | none | high | None | seed901..seed964 | 128 | 1264 | 0 | +3.79 [+2.82, +4.74] | PASS |  |
| d3w_setfull_high | set_full_s0 | prefix | high | None | seed901..seed964 | 128 | 1213 | 5158 | -0.41 [-1.37, +0.46] | PASS |  |
| d3w_setfull_high_freshonly | set_full_s0 | prefix | high | None | seed901..seed964 | 128 | 1182 | 5159 | -2.94 [-3.79, -1.97] | PASS |  |
| d4_fo_orders | set_full_s0 | nbr | iid | None | seed901..seed964 | 128 | 1212 | 5309 | -0.48 [-1.31, +0.43] | PASS |  |
| d4_fo_orders | set_full_s0 | random | iid | None | seed901..seed964 | 128 | 1213 | 4900 | -0.46 [-1.49, +0.60] | PASS |  |
| d4_fo_orders | set_full_s0 | rxold | iid | None | seed901..seed964 | 128 | 1210 | 5356 | -0.66 [-1.47, +0.23] | PASS |  |
| d4_fo_orders | set_full_s0 | rxq | iid | None | seed901..seed964 | 128 | 1214 | 5308 | -0.35 [-1.14, +0.53] | PASS |  |
| d4_last_def | set_full_s0_last | full | iid | None | seed901..seed964 | 128 | 1197 | 5850 | -1.73 [-2.58, -0.84] | PASS |  |
| d4_last_def | set_none_s0_last | full | iid | None | seed901..seed964 | 128 | 1277 | 5850 | +4.82 [+3.79, +5.82] | PASS |  |
| d4_last_def | set_full_s0_last | none | iid | None | seed901..seed964 | 128 | 1254 | 0 | +2.93 [+1.86, +3.97] | PASS |  |
| d4_last_def | set_none_s0_last | none | iid | None | seed901..seed964 | 128 | 1268 | 0 | +4.10 [+3.08, +5.15] | PASS |  |
| d4_last_fo | set_full_s0_last | cap4 | iid | None | seed901..seed964 | 128 | 1208 | 2600 | -0.80 [-1.78, +0.20] | PASS |  |
| d4_last_fo | set_full_s0_last | prefix | iid | None | seed901..seed964 | 128 | 1216 | 4904 | -0.17 [-1.11, +0.79] | PASS |  |
| d5_q16_bc5_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1187 | 5850 | -2.52 [-3.30, -1.73] | PASS |  |
| d5_q16_full | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1183 | 5850 | -2.87 [-3.75, -2.03] | PASS |  |
| d5_q2_bc2_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1180 | 5850 | -3.13 [-4.24, -2.05] | PASS |  |
| d5_q2_full | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1180 | 5850 | -3.13 [-4.24, -2.05] | PASS |  |
| d5_q4_bc3_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1175 | 5850 | -3.54 [-4.58, -2.49] | PASS |  |
| d5_q4_full | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1175 | 5850 | -3.54 [-4.58, -2.49] | PASS |  |
| d5_q8_bc4_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1177 | 5850 | -3.37 [-4.20, -2.54] | PASS |  |
| d5_q8_full | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1178 | 5850 | -3.28 [-4.16, -2.42] | PASS |  |
| d6_flatfull_high_freshonly | full_s0 | prefix | high | None | seed901..seed964 | 128 | 1256 | 5158 | +3.11 [+2.02, +4.22] | PASS |  |
| d6_flatfull_high_freshonly | full_s1 | prefix | high | None | seed901..seed964 | 128 | 1218 | 5158 | +2.79 [+1.67, +3.76] | PASS |  |
| d7_flatfull_q4_bc3_fo | full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1249 | 5850 | +2.51 [+1.54, +3.51] | PASS |  |
| d7_flatfull_q4_bc3_fo | full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1198 | 5850 | +1.08 [+0.10, +1.97] | PASS |  |
| d7_setfull_q4_bc12_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1197 | 5848 | -1.70 [-2.52, -0.90] | PASS |  |
| d7_setfull_q4_bc25_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1215 | 4908 | -0.24 [-1.21, +0.71] | PASS |  |
| d7_setfull_q4_bc6_fo | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1183 | 5850 | -2.92 [-3.81, -2.00] | PASS |  |
| diag_flat_freshonly | scratch_s3 | prefix | iid | None | seed901..seed964 | 128 | 1429 | 4906 | +17.69 [+16.59, +18.82] | PASS |  |
| diag_flat_freshonly | scratch_rs_s0 | prefix | iid | None | seed901..seed964 | 128 | 1365 | 4906 | +12.04 [+10.77, +13.25] | PASS |  |
| distill_fo_prefix_s0 | distill_fo_prefix_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1194 | 2600 | -1.98 [-3.04, -0.96] | PASS |  |
| distill_fo_prefix_s0 | distill_fo_prefix_s0 | none | iid | None | seed901..seed964 | 128 | 1270 | 0 | +4.27 [+3.30, +5.24] | PASS |  |
| distill_fo_prefix_s0 | distill_fo_prefix_s0 | prefix | iid | None | seed901..seed964 | 128 | 1193 | 4906 | -2.07 [-3.06, -1.10] | PASS |  |
| distill_none_fromnone_s0 | distill_none_fromnone_s0 | none | iid | None | seed901..seed964 | 128 | 1261 | 0 | +3.54 [+2.62, +4.44] | PASS |  |
| distill_none_fromnone_s1 | distill_none_fromnone_s1 | none | iid | None | seed901..seed964 | 128 | 1261 | 0 | +6.45 [+5.45, +7.40] | PASS |  |
| distill_none_fromnone_s2 | distill_none_fromnone_s2 | none | iid | None | seed901..seed964 | 128 | 1255 | 0 | +3.22 [+2.27, +4.22] | PASS |  |
| distill_none_fromprefix_s0 | distill_none_fromprefix_s0 | none | iid | None | seed901..seed964 | 128 | 1230 | 0 | +0.94 [-0.07, +1.97] | PASS |  |
| distill_none_fromprefix_s1 | distill_none_fromprefix_s1 | none | iid | None | seed901..seed964 | 128 | 1253 | 0 | +5.72 [+4.74, +6.65] | PASS |  |
| distill_none_rep_s0 | distill_none_rep_s0 | none | iid | None | seed901..seed964 | 128 | 1215 | 0 | -0.26 [-1.05, +0.55] | PASS |  |
| distill_none_rep_s1 | distill_none_rep_s1 | none | iid | None | seed901..seed964 | 128 | 1171 | 0 | -1.20 [-2.00, -0.48] | PASS |  |
| distill_none_rep_s2 | distill_none_rep_s2 | none | iid | None | seed901..seed964 | 128 | 1206 | 0 | -0.86 [-1.82, -0.02] | PASS |  |
| distill_none_rep_s3 | distill_none_rep_s3 | none | iid | None | seed901..seed964 | 128 | 1219 | 0 | +0.35 [-0.48, +1.10] | PASS |  |
| distill_none_rep_s4 | distill_none_rep_s4 | none | iid | None | seed901..seed964 | 128 | 1207 | 0 | -0.19 [-0.99, +0.62] | PASS |  |
| distill_none_rep_s5 | distill_none_rep_s5 | none | iid | None | seed901..seed964 | 128 | 1210 | 0 | -0.64 [-1.46, +0.25] | PASS |  |
| distill_none_rep_s6 | distill_none_rep_s6 | none | iid | None | seed901..seed964 | 128 | 1236 | 0 | -0.14 [-0.72, +0.45] | PASS |  |
| distill_none_rep_s7 | distill_none_rep_s7 | none | iid | None | seed901..seed964 | 128 | 1158 | 0 | +0.21 [-0.66, +1.10] | PASS |  |
| distill_none_rep_s8 | distill_none_rep_s8 | none | iid | None | seed901..seed964 | 128 | 1269 | 0 | -0.15 [-0.81, +0.58] | PASS |  |
| distill_none_rep_s9 | distill_none_rep_s9 | none | iid | None | seed901..seed964 | 128 | 1232 | 0 | -0.08 [-0.87, +0.67] | PASS |  |
| distill_none_s0 | distill_none_s0 | none | iid | None | seed901..seed964 | 128 | 1218 | 0 | — | PASS |  |
| distill_none_s1 | distill_none_s1 | none | iid | None | seed901..seed964 | 128 | 1185 | 0 | — | PASS |  |
| distill_none_s2 | distill_none_s2 | none | iid | None | seed901..seed964 | 128 | 1216 | 0 | — | PASS |  |
| distill_none_s3 | distill_none_s3 | none | iid | None | seed901..seed964 | 128 | 1215 | 0 | — | PASS |  |
| distill_none_s4 | distill_none_s4 | none | iid | None | seed901..seed964 | 128 | 1209 | 0 | — | PASS |  |
| distill_none_s5 | distill_none_s5 | none | iid | None | seed901..seed964 | 128 | 1217 | 0 | — | PASS |  |
| distill_none_s6 | distill_none_s6 | none | iid | None | seed901..seed964 | 128 | 1238 | 0 | — | PASS |  |
| distill_none_s7 | distill_none_s7 | none | iid | None | seed901..seed964 | 128 | 1156 | 0 | — | PASS |  |
| distill_none_s8 | distill_none_s8 | none | iid | None | seed901..seed964 | 128 | 1271 | 0 | — | PASS |  |
| distill_none_s9 | distill_none_s9 | none | iid | None | seed901..seed964 | 128 | 1233 | 0 | — | PASS |  |
| fixcap_s0 | fixcap_s0 | none | fixed | None | seed901..seed964 | 128 | 1329 | 0 | +9.09 [+8.08, +10.08] | PASS |  |
| fixcap_s0 | fixcap_s0 | prefix | fixed | None | seed901..seed964 | 128 | 1377 | 4856 | +13.04 [+11.87, +14.14] | PASS |  |
| full_s0_eval | full_s0_eval | full | None | None | seed901..seed964 | 128 | 1250 | 5850 | +2.60 [+1.54, +3.71] | PASS |  |
| full_s0_eval | full_s0_eval | none | None | None | seed901..seed964 | 128 | 1447 | 0 | +18.81 [+17.49, +20.11] | PASS |  |
| full_s0_eval | full_s0_eval | prefix | None | None | seed901..seed964 | 128 | 1405 | 4903 | +15.36 [+14.03, +16.77] | PASS |  |
| full_s1 | full_s1 | full | None | None | seed901..seed964 | 128 | 1199 | 5850 | +1.17 [+0.24, +2.09] | PASS |  |
| full_s1 | full_s1 | none | None | None | seed901..seed964 | 128 | 1469 | 0 | +23.99 [+22.65, +25.36] | PASS |  |
| full_s1 | full_s1 | prefix | None | None | seed901..seed964 | 128 | 1409 | 4906 | +18.90 [+17.72, +20.07] | PASS |  |
| nbr_s0 | nbr_s0 | nbr | None | None | seed901..seed964 | 128 | 1364 | 5308 | +12.00 [+10.70, +13.33] | PASS |  |
| nbr_s0 | nbr_s0 | prefix | None | None | seed901..seed964 | 128 | 1362 | 4909 | +11.85 [+10.71, +12.99] | PASS |  |
| nbrmask_s0 | nbrmask_s0 | nbr | None | None | seed901..seed964 | 128 | 1280 | 5302 | +5.07 [+4.02, +6.10] | PASS |  |
| nbrmask_s0 | nbrmask_s0 | prefix | None | None | seed901..seed964 | 128 | 1302 | 4906 | +6.89 [+5.88, +7.96] | PASS |  |
| nbrmask_s1 | nbrmask_s1 | nbr | iid | None | seed901..seed964 | 128 | 1334 | 5307 | +12.62 [+11.56, +13.58] | PASS |  |
| nbrmask_s1 | nbrmask_s1 | none | iid | None | seed901..seed964 | 128 | 1390 | 0 | +17.36 [+16.17, +18.50] | PASS |  |
| nbrmask_s1 | nbrmask_s1 | prefix | iid | None | seed901..seed964 | 128 | 1362 | 4905 | +14.95 [+13.87, +16.01] | PASS |  |
| none_s0 | none_s0 | none | None | None | seed901..seed964 | 128 | 1293 | 0 | +6.17 [+5.16, +7.21] | PASS |  |
| none_s0 | none_s0 | prefix | None | None | seed901..seed964 | 128 | 1300 | 4902 | +6.73 [+5.67, +7.73] | PASS |  |
| none_s0_cont4000 | none_s0_cont4000 | none | None | None | seed901..seed964 | 128 | 1264 | 0 | +3.78 [+2.77, +4.79] | PASS |  |
| none_s1 | none_s1 | none | None | None | seed901..seed964 | 128 | 1290 | 0 | +8.90 [+7.91, +9.85] | PASS |  |
| p3_cbB_setfull | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1174 | 5850 | -3.59 [-4.60, -2.53] | PASS |  |
| p3_cbB_setfull | set_full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1133 | 5850 | -4.41 [-5.26, -3.53] | PASS |  |
| p4_loss0.1_flat | full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1197 | 5850 | +1.05 [-0.02, +2.08] | PASS |  |
| p4_loss0.1_q4t | set_fullq4_s0 | prefix | iid | None | seed901..seed964 | 128 | 1158 | 5850 | -4.93 [-5.78, -4.10] | PASS |  |
| p4_loss0.1_q4t | set_fullq4_s1 | prefix | iid | None | seed901..seed964 | 128 | 1141 | 5850 | -3.70 [-4.59, -2.87] | PASS |  |
| p4_loss0.25_flat | full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1217 | 5850 | +2.75 [+1.63, +3.81] | PASS |  |
| p4_loss0.25_q4t | set_fullq4_s0 | prefix | iid | None | seed901..seed964 | 128 | 1163 | 5850 | -4.51 [-5.40, -3.61] | PASS |  |
| p4_loss0.25_q4t | set_fullq4_s1 | prefix | iid | None | seed901..seed964 | 128 | 1155 | 5850 | -2.47 [-3.48, -1.50] | PASS |  |
| p4_loss0.5_flat | full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1322 | 5850 | +11.62 [+10.50, +12.72] | PASS |  |
| p4_loss0.5_q4t | set_fullq4_s0 | prefix | iid | None | seed901..seed964 | 128 | 1209 | 5850 | -0.78 [-1.85, +0.25] | PASS |  |
| p4_loss0.5_q4t | set_fullq4_s1 | prefix | iid | None | seed901..seed964 | 128 | 1182 | 5850 | -0.25 [-1.28, +0.78] | PASS |  |
| prefix_s0_cont4000 | prefix_s0_cont4000 | none | None | None | seed901..seed964 | 128 | 1446 | 0 | +18.72 [+17.52, +19.96] | PASS |  |
| prefix_s0_cont4000 | prefix_s0_cont4000 | prefix | None | None | seed901..seed964 | 128 | 1337 | 4909 | +9.75 [+8.76, +10.76] | PASS |  |
| q4t_bc3_fo | set_fullq4_s0 | prefix | iid | None | seed901..seed964 | 128 | 1162 | 5850 | -4.61 [-5.40, -3.83] | PASS |  |
| q4t_full | set_fullq4_s0 | full | iid | None | seed901..seed964 | 128 | 1162 | 5850 | -4.61 [-5.40, -3.83] | PASS |  |
| q4t_full | set_fullq4_s0 | none | iid | None | seed901..seed964 | 128 | 1268 | 0 | +4.10 [+3.16, +5.06] | PASS |  |
| q4t_packet_fo | set_fullq4_s0 | prefix | iid | None | seed901..seed964 | 128 | 1206 | 4905 | -1.03 [-1.92, -0.16] | PASS |  |
| q4t_s1_bc3_fo | set_fullq4_s1 | prefix | iid | None | seed901..seed964 | 128 | 1134 | 5850 | -4.30 [-5.20, -3.41] | PASS |  |
| q4t_s1_full | set_fullq4_s1 | full | iid | None | seed901..seed964 | 128 | 1134 | 5850 | -4.30 [-5.20, -3.41] | PASS |  |
| q4t_s1_full | set_fullq4_s1 | none | iid | None | seed901..seed964 | 128 | 1220 | 0 | +2.99 [+1.84, +4.11] | PASS |  |
| q4t_s2_bc3_fo | set_fullq4_s2 | prefix | iid | None | seed901..seed964 | 128 | 1278 | 5850 | +5.07 [+3.88, +6.23] | PASS |  |
| rand_s0 | rand_s0 | none | iid | None | seed901..seed964 | 128 | 1452 | 0 | +19.23 [+18.13, +20.36] | PASS |  |
| rand_s0 | rand_s0 | prefix | iid | None | seed901..seed964 | 128 | 1418 | 4902 | +16.44 [+15.00, +17.91] | PASS |  |
| rand_s0 | rand_s0 | random | iid | None | seed901..seed964 | 128 | 1387 | 4900 | +13.88 [+12.64, +15.08] | PASS |  |
| rc_attn_s0 | rc_attn_s0 | none | iid | None | seed901..seed964 | 128 | 1238 | 0 | +1.66 [+0.75, +2.61] | PASS |  |
| rc_attn_s0 | rc_attn_s0 | prefix | iid | None | seed901..seed964 | 128 | 1236 | 4906 | +1.48 [+0.52, +2.51] | PASS |  |
| rc_fresh_s0 | rc_fresh_s0 | none | iid | None | seed901..seed964 | 128 | 1343 | 0 | +10.24 [+9.14, +11.33] | PASS |  |
| rc_fresh_s0 | rc_fresh_s0 | prefix | iid | None | seed901..seed964 | 128 | 1377 | 4907 | +13.06 [+12.03, +14.14] | PASS |  |
| rc_h256_s0 | rc_h256_s0 | none | iid | None | seed901..seed964 | 128 | 1776 | 0 | +45.79 [+44.24, +47.39] | PASS |  |
| rc_h256_s0 | rc_h256_s0 | prefix | iid | None | seed901..seed964 | 128 | 1368 | 4904 | +12.34 [+11.06, +13.67] | PASS |  |
| rc_noise_s0 | rc_noise_s0 | none | iid | None | seed901..seed964 | 128 | 1279 | 0 | +5.00 [+3.93, +5.96] | PASS |  |
| rc_sconcat_s0 | rc_sconcat_s0 | none | iid | None | seed901..seed964 | 128 | 1290 | 0 | +5.92 [+4.83, +7.01] | PASS |  |
| rc_sconcat_s0 | rc_sconcat_s0 | prefix | iid | None | seed901..seed964 | 128 | 1341 | 4905 | +10.12 [+8.88, +11.40] | PASS |  |
| refprefix_cap_fixed | scratch_s3 | prefix | fixed | None | seed901..seed964 | 128 | 1406 | 4843 | +15.74 [+14.13, +17.38] | PASS |  |
| refprefix_cap_fixed | scratch_rs_s0 | prefix | fixed | None | seed901..seed964 | 128 | 1389 | 4826 | +14.06 [+12.69, +15.40] | PASS |  |
| refprefix_cap_high | scratch_s3 | prefix | high | None | seed901..seed964 | 128 | 1361 | 5158 | +12.08 [+10.97, +13.25] | PASS |  |
| refprefix_cap_high | scratch_rs_s0 | prefix | high | None | seed901..seed964 | 128 | 1364 | 5156 | +11.97 [+10.77, +13.16] | PASS |  |
| relay6A4_st_s0_eval | relay6A4_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1180 | 2600 | -3.17 [-4.06, -2.29] | PASS |  |
| relay6A4_st_s0_eval | relay6A4_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1179 | 4907 | -3.23 [-4.05, -2.39] | PASS |  |
| relay6A4_st_s1_eval | relay6A4_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1188 | 2600 | +0.31 [-0.68, +1.22] | PASS |  |
| relay6A4_st_s1_eval | relay6A4_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1144 | 4903 | -3.44 [-4.36, -2.50] | PASS |  |
| relay6A504_st_s0_eval | relay6A504_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1223 | 2600 | +0.39 [-0.43, +1.26] | PASS |  |
| relay6A504_st_s0_eval | relay6A504_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1191 | 4907 | -2.24 [-3.02, -1.54] | PASS |  |
| relay6A504_st_s1_eval | relay6A504_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1174 | 2600 | -0.93 [-1.78, -0.07] | PASS |  |
| relay6A504_st_s1_eval | relay6A504_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1140 | 4904 | -3.81 [-4.64, -3.00] | PASS |  |
| relay6B16_st_s0_eval | relay6B16_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1206 | 2600 | -0.98 [-1.82, -0.14] | PASS |  |
| relay6B16_st_s0_eval | relay6B16_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1182 | 4909 | -2.93 [-3.72, -2.14] | PASS |  |
| relay6B16_st_s1_eval | relay6B16_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1160 | 2600 | -2.09 [-2.82, -1.36] | PASS |  |
| relay6B16_st_s1_eval | relay6B16_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1141 | 4905 | -3.65 [-4.44, -2.84] | PASS |  |
| relay6B8_st_s0_eval | relay6B8_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1202 | 2600 | -1.35 [-2.28, -0.39] | PASS |  |
| relay6B8_st_s0_eval | relay6B8_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1182 | 4908 | -2.94 [-3.81, -2.14] | PASS |  |
| relay6B8_st_s1_eval | relay6B8_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1141 | 2600 | -3.71 [-4.52, -2.91] | PASS |  |
| relay6B8_st_s1_eval | relay6B8_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1136 | 4904 | -4.12 [-4.88, -3.36] | PASS |  |
| relay6Cage_st_s0_eval | relay6Cage_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1183 | 4902 | -2.85 [-3.81, -1.84] | PASS |  |
| relay6Cage_st_s0_evprefix | relay6Cage_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1190 | 4904 | -2.28 [-3.13, -1.41] | PASS |  |
| relay6Cage_st_s1_eval | relay6Cage_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1146 | 4902 | -3.25 [-4.00, -2.45] | PASS |  |
| relay6Cage_st_s1_evprefix | relay6Cage_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1150 | 4905 | -2.92 [-3.80, -2.06] | PASS |  |
| relay6Clow_st_s0_eval | relay6Clow_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1177 | 2600 | -3.36 [-4.19, -2.50] | PASS |  |
| relay6Clow_st_s0_eval | relay6Clow_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1186 | 4906 | -2.61 [-3.36, -1.85] | PASS |  |
| relay6Clow_st_s0_evlow | relay6Clow_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1182 | 2409 | -2.94 [-3.77, -2.04] | PASS |  |
| relay6Clow_st_s1_eval | relay6Clow_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1138 | 2600 | -3.96 [-4.70, -3.25] | PASS |  |
| relay6Clow_st_s1_eval | relay6Clow_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1165 | 4904 | -1.64 [-2.56, -0.77] | PASS |  |
| relay6Clow_st_s1_evlow | relay6Clow_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1135 | 2408 | -4.19 [-4.91, -3.44] | PASS |  |
| relay6_st_s0_eval | relay6_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1212 | 2600 | -0.47 [-1.34, +0.36] | PASS |  |
| relay6_st_s0_eval | relay6_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1187 | 4905 | -2.59 [-3.46, -1.72] | PASS |  |
| relay6_st_s0_evlow | relay6_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1221 | 2406 | +0.27 [-0.55, +1.16] | PASS |  |
| relay6_st_s1_eval | relay6_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1190 | 2600 | +0.44 [-0.44, +1.35] | PASS |  |
| relay6_st_s1_eval | relay6_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1138 | 4904 | -3.96 [-4.77, -3.18] | PASS |  |
| relay6_st_s1_evlow | relay6_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1196 | 2407 | +0.97 [+0.04, +1.83] | PASS |  |
| relay_ppo_s0_eval | relay_ppo_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1237 | 2599 | +1.57 [+0.55, +2.58] | PASS |  |
| relay_ppo_s0_eval | relay_ppo_s0 | prefix | iid | None | seed901..seed964 | 128 | 1242 | 4908 | +1.99 [+0.89, +3.13] | PASS |  |
| relay_ppo_s0_none | relay_ppo_s0 | none | iid | None | seed901..seed964 | 128 | 1228 | 0 | +0.80 [-0.10, +1.72] | PASS |  |
| relay_ppo_s1_eval | relay_ppo_s1 | cap4 | iid | None | seed901..seed964 | 128 | 1243 | 2600 | +4.92 [+4.04, +5.79] | PASS |  |
| relay_ppo_s1_eval | relay_ppo_s1 | prefix | iid | None | seed901..seed964 | 128 | 1239 | 4901 | +4.54 [+3.48, +5.64] | PASS |  |
| relay_ppo_s1_none | relay_ppo_s1 | none | iid | None | seed901..seed964 | 128 | 1238 | 0 | +4.46 [+3.42, +5.41] | PASS |  |
| relay_st_s0_eval | relay_st_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1239 | 2600 | +1.68 [+0.72, +2.63] | PASS |  |
| relay_st_s0_eval | relay_st_s0 | prefix | iid | None | seed901..seed964 | 128 | 1178 | 4902 | -3.33 [-4.19, -2.49] | PASS |  |
| relay_st_s0_none | relay_st_s0 | none | iid | None | seed901..seed964 | 128 | 1276 | 0 | +4.79 [+3.69, +5.91] | PASS |  |
| relay_st_s0_sat | relay_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1230 | 2600 | +0.94 [+0.01, +1.89] | PASS |  |
| relay_st_s0_sat | relay_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1178 | 4902 | -3.26 [-4.18, -2.40] | PASS |  |
| relay_st_s1_eval | relay_st_s1 | prefix | iid | None | seed901..seed964 | 128 | 1137 | 4902 | -4.03 [-4.96, -3.18] | PASS |  |
| relay_st_s1_none | relay_st_s1 | none | iid | None | seed901..seed964 | 128 | 1235 | 0 | +4.24 [+3.39, +5.07] | PASS |  |
| relay_st_s1_sat | relay_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1166 | 2600 | -1.61 [-2.58, -0.70] | PASS |  |
| relay_st_s1_sat | relay_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1138 | 4902 | -3.95 [-4.85, -3.08] | PASS |  |
| set_fresh_s0 | set_fresh_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1187 | 2600 | -2.60 [-3.56, -1.64] | PASS |  |
| set_fresh_s0 | set_fresh_s0 | none | iid | None | seed901..seed964 | 128 | 1227 | 0 | +0.71 [-0.25, +1.73] | PASS |  |
| set_fresh_s0 | set_fresh_s0 | prefix | iid | None | seed901..seed964 | 128 | 1185 | 4905 | -2.71 [-3.64, -1.71] | PASS |  |
| set_fresh_s2 | set_fresh_s2 | cap4 | iid | None | seed901..seed964 | 128 | 1245 | 2600 | +2.38 [+1.48, +3.27] | PASS |  |
| set_fresh_s2 | set_fresh_s2 | none | iid | None | seed901..seed964 | 128 | 1245 | 0 | +2.36 [+1.35, +3.34] | PASS |  |
| set_fresh_s2 | set_fresh_s2 | prefix | iid | None | seed901..seed964 | 128 | 1228 | 4909 | +1.00 [+0.06, +1.97] | PASS |  |
| set_fresh_s3 | set_fresh_s3 | cap4 | iid | None | seed901..seed964 | 128 | 1282 | 2600 | +5.53 [+4.63, +6.42] | PASS |  |
| set_fresh_s3 | set_fresh_s3 | none | iid | None | seed901..seed964 | 128 | 1250 | 0 | +2.89 [+1.93, +3.84] | PASS |  |
| set_fresh_s3 | set_fresh_s3 | prefix | iid | None | seed901..seed964 | 128 | 1233 | 4908 | +1.53 [+0.55, +2.49] | PASS |  |
| set_full_s0 | set_full_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1281 | 2600 | +5.19 [+4.14, +6.24] | PASS |  |
| set_full_s0 | set_full_s0 | cap6 | iid | None | seed901..seed964 | 128 | 1279 | 3884 | +5.02 [+3.99, +6.06] | PASS |  |
| set_full_s0 | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1185 | 5850 | -2.74 [-3.63, -1.86] | PASS |  |
| set_full_s0 | set_full_s0 | none | iid | None | seed901..seed964 | 128 | 1264 | 0 | +3.79 [+2.82, +4.74] | PASS |  |
| set_full_s0 | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1258 | 4905 | +3.24 [+2.18, +4.32] | PASS |  |
| set_full_s1 | set_full_s1 | full | iid | None | seed901..seed964 | 128 | 1137 | 5850 | -4.05 [-4.90, -3.24] | PASS |  |
| set_full_s1 | set_full_s1 | none | iid | None | seed901..seed964 | 128 | 1220 | 0 | +2.97 [+2.01, +3.86] | PASS |  |
| set_full_s1 | set_full_s1 | prefix | iid | None | seed901..seed964 | 128 | 1260 | 4905 | +6.32 [+5.40, +7.18] | PASS |  |
| set_full_s2 | set_full_s2 | full | iid | None | seed901..seed964 | 128 | 1162 | 5850 | -4.44 [-5.27, -3.60] | PASS |  |
| set_full_s2 | set_full_s2 | none | iid | None | seed901..seed964 | 128 | 1271 | 0 | +4.52 [+3.56, +5.47] | PASS |  |
| set_full_s2 | set_full_s2 | prefix | iid | None | seed901..seed964 | 128 | 1285 | 4905 | +5.62 [+4.59, +6.63] | PASS |  |
| set_full_s3 | set_full_s3 | full | iid | None | seed901..seed964 | 128 | 1187 | 5850 | -2.25 [-3.15, -1.36] | PASS |  |
| set_full_s3 | set_full_s3 | none | iid | None | seed901..seed964 | 128 | 1247 | 0 | +2.65 [+1.55, +3.68] | PASS |  |
| set_full_s3 | set_full_s3 | prefix | iid | None | seed901..seed964 | 128 | 1241 | 4905 | +2.14 [+1.05, +3.23] | PASS |  |
| set_full_s4 | set_full_s4 | full | iid | None | seed901..seed964 | 128 | 1176 | 5850 | -2.76 [-3.62, -1.89] | PASS |  |
| set_full_s4 | set_full_s4 | none | iid | None | seed901..seed964 | 128 | 1267 | 0 | +4.80 [+3.81, +5.82] | PASS |  |
| set_full_s4 | set_full_s4 | prefix | iid | None | seed901..seed964 | 128 | 1274 | 4906 | +5.32 [+4.31, +6.39] | PASS |  |
| set_full_s5 | set_full_s5 | full | iid | None | seed901..seed964 | 128 | 1219 | 5850 | +0.18 [-0.66, +1.03] | PASS |  |
| set_full_s5 | set_full_s5 | none | iid | None | seed901..seed964 | 128 | 1222 | 0 | +0.38 [-0.57, +1.27] | PASS |  |
| set_full_s5 | set_full_s5 | prefix | iid | None | seed901..seed964 | 128 | 1251 | 4903 | +2.81 [+1.84, +3.79] | PASS |  |
| set_full_s6 | set_full_s6 | full | iid | None | seed901..seed964 | 128 | 1224 | 5850 | -1.13 [-1.83, -0.44] | PASS |  |
| set_full_s6 | set_full_s6 | none | iid | None | seed901..seed964 | 128 | 1235 | 0 | -0.21 [-1.09, +0.66] | PASS |  |
| set_full_s6 | set_full_s6 | prefix | iid | None | seed901..seed964 | 128 | 1257 | 4907 | +1.52 [+0.61, +2.40] | PASS |  |
| set_full_s7 | set_full_s7 | full | iid | None | seed901..seed964 | 128 | 1118 | 5850 | -3.27 [-3.89, -2.59] | PASS |  |
| set_full_s7 | set_full_s7 | none | iid | None | seed901..seed964 | 128 | 1219 | 0 | +5.47 [+4.41, +6.60] | PASS |  |
| set_full_s7 | set_full_s7 | prefix | iid | None | seed901..seed964 | 128 | 1214 | 4907 | +4.98 [+3.94, +6.04] | PASS |  |
| set_full_s8 | set_full_s8 | full | iid | None | seed901..seed964 | 128 | 1257 | 5850 | -1.07 [-1.93, -0.15] | PASS |  |
| set_full_s8 | set_full_s8 | none | iid | None | seed901..seed964 | 128 | 1270 | 0 | -0.08 [-0.90, +0.77] | PASS |  |
| set_full_s8 | set_full_s8 | prefix | iid | None | seed901..seed964 | 128 | 1274 | 4905 | +0.20 [-0.55, +1.05] | PASS |  |
| set_full_s9 | set_full_s9 | full | iid | None | seed901..seed964 | 128 | 1232 | 5850 | -0.09 [-0.99, +0.79] | PASS |  |
| set_full_s9 | set_full_s9 | none | iid | None | seed901..seed964 | 128 | 1233 | 0 | +0.00 [-0.69, +0.73] | PASS |  |
| set_full_s9 | set_full_s9 | prefix | iid | None | seed901..seed964 | 128 | 1244 | 4905 | +0.88 [+0.10, +1.73] | PASS |  |
| set_nbr_s0 | set_nbr_s0 | nbr | iid | None | seed901..seed964 | 128 | 1244 | 5308 | +2.12 [+1.20, +3.02] | PASS |  |
| set_nbr_s0 | set_nbr_s0 | none | iid | None | seed901..seed964 | 128 | 1242 | 0 | +1.94 [+1.02, +2.90] | PASS |  |
| set_nbr_s0 | set_nbr_s0 | prefix | iid | None | seed901..seed964 | 128 | 1247 | 4908 | +2.39 [+1.44, +3.39] | PASS |  |
| set_none_s0 | set_none_s0 | none | iid | None | seed901..seed964 | 128 | 1258 | 0 | +3.30 [+2.36, +4.21] | PASS |  |
| set_none_s0 | set_none_s0 | prefix | iid | None | seed901..seed964 | 128 | 1272 | 4904 | +4.45 [+3.52, +5.36] | PASS |  |
| set_none_s0_cont2500 | set_none_s0_cont2500 | none | iid | None | seed901..seed964 | 128 | 1283 | 0 | +5.33 [+4.34, +6.34] | PASS |  |
| set_none_s1 | set_none_s1 | none | iid | None | seed901..seed964 | 128 | 1264 | 0 | +6.68 [+5.66, +7.63] | PASS |  |
| set_none_s1 | set_none_s1 | prefix | iid | None | seed901..seed964 | 128 | 1246 | 4903 | +5.20 [+4.23, +6.22] | PASS |  |
| set_none_s2 | set_none_s2 | none | iid | None | seed901..seed964 | 128 | 1253 | 0 | +3.04 [+2.15, +3.95] | PASS |  |
| set_none_s2 | set_none_s2 | prefix | iid | None | seed901..seed964 | 128 | 1273 | 4907 | +4.67 [+3.54, +5.73] | PASS |  |
| set_none_s3 | set_none_s3 | none | iid | None | seed901..seed964 | 128 | 1248 | 0 | +2.76 [+1.78, +3.78] | PASS |  |
| set_none_s4 | set_none_s4 | none | iid | None | seed901..seed964 | 128 | 1237 | 0 | +2.29 [+1.32, +3.36] | PASS |  |
| set_none_s5 | set_none_s5 | none | iid | None | seed901..seed964 | 128 | 1238 | 0 | +1.66 [+0.74, +2.65] | PASS |  |
| set_none_s6 | set_none_s6 | none | iid | None | seed901..seed964 | 128 | 1253 | 0 | +1.23 [+0.45, +1.99] | PASS |  |
| set_none_s7 | set_none_s7 | none | iid | None | seed901..seed964 | 128 | 1243 | 0 | +7.57 [+6.52, +8.66] | PASS |  |
| set_none_s8 | set_none_s8 | none | iid | None | seed901..seed964 | 128 | 1230 | 0 | -3.25 [-4.10, -2.38] | PASS |  |
| set_none_s9 | set_none_s9 | none | iid | None | seed901..seed964 | 128 | 1249 | 0 | +1.31 [+0.48, +2.24] | PASS |  |
| set_prefix_s0 | set_prefix_s0 | none | iid | None | seed901..seed964 | 128 | 1237 | 0 | +1.54 [+0.63, +2.51] | PASS |  |
| set_prefix_s0 | set_prefix_s0 | prefix | iid | None | seed901..seed964 | 128 | 1233 | 4906 | +1.22 [+0.22, +2.23] | PASS |  |
| set_prefix_s0_frontier | set_prefix_s0 | cap2 | iid | None | seed901..seed964 | 128 | 1278 | 1300 | +4.89 [+3.92, +5.88] | PASS |  |
| set_prefix_s0_frontier | set_prefix_s0 | cap4 | iid | None | seed901..seed964 | 128 | 1304 | 2600 | +7.03 [+5.95, +8.23] | PASS |  |
| set_prefix_s0_frontier | set_prefix_s0 | cap6 | iid | None | seed901..seed964 | 128 | 1276 | 3884 | +4.77 [+3.62, +5.91] | PASS |  |
| set_prefix_s0_frontier | set_prefix_s0 | full | iid | None | seed901..seed964 | 128 | 1239 | 5850 | +1.74 [+0.81, +2.67] | PASS |  |
| set_prefix_s1 | set_prefix_s1 | none | iid | None | seed901..seed964 | 128 | 1271 | 0 | +7.28 [+6.18, +8.30] | PASS |  |
| set_prefix_s1 | set_prefix_s1 | prefix | iid | None | seed901..seed964 | 128 | 1260 | 4907 | +6.37 [+5.29, +7.34] | PASS |  |
| set_rand_s0 | set_rand_s0 | none | iid | None | seed901..seed964 | 128 | 1254 | 0 | +2.93 [+1.96, +3.83] | PASS |  |
| set_rand_s0 | set_rand_s0 | prefix | iid | None | seed901..seed964 | 128 | 1252 | 4908 | +2.77 [+1.85, +3.76] | PASS |  |
| set_rand_s0 | set_rand_s0 | random | iid | None | seed901..seed964 | 128 | 1247 | 4900 | +2.33 [+1.45, +3.21] | PASS |  |
| set_rxq_s0 | set_rxq_s0 | none | iid | None | seed901..seed964 | 128 | 1228 | 0 | +0.79 [-0.23, +1.78] | PASS |  |
| set_rxq_s0 | set_rxq_s0 | prefix | iid | None | seed901..seed964 | 128 | 1241 | 4903 | +1.87 [+0.90, +2.81] | PASS |  |
| set_rxq_s0 | set_rxq_s0 | rxq | iid | None | seed901..seed964 | 128 | 1239 | 5314 | +1.68 [+0.76, +2.62] | PASS |  |
| set_rxq_s1 | set_rxq_s1 | none | iid | None | seed901..seed964 | 128 | 1253 | 0 | +5.73 [+4.74, +6.70] | PASS |  |
| set_rxq_s1 | set_rxq_s1 | prefix | iid | None | seed901..seed964 | 128 | 1251 | 4904 | +5.58 [+4.62, +6.46] | PASS |  |
| set_rxq_s1 | set_rxq_s1 | rxq | iid | None | seed901..seed964 | 128 | 1242 | 5306 | +4.83 [+3.89, +5.75] | PASS |  |

## e3_codesign_full_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| full_s0 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1361 | 3250 | +11.77 [+10.46, +13.03] | PASS |  |
| full_s0 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1294 | 3900 | +6.20 [+5.04, +7.43] | PASS |  |
| full_s0 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1264 | 4550 | +3.78 [+2.70, +4.89] | PASS |  |
| full_s0 | ? | cap_8 | iid | None | seed901..seed964 | 128 | 1268 | 5200 | +4.07 [+3.00, +5.24] | PASS |  |
| full_s0 | ? | prefix | iid | None | seed901..seed964 | 128 | 1250 | 5850 | +2.60 [+1.54, +3.71] | PASS |  |
| full_s0 | ? | proxy | iid | None | seed901..seed964 | 128 | 1404 | 3508 | +15.29 [+13.78, +16.73] | PASS |  |
| full_s0 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1401 | 3564 | +15.03 [+13.56, +16.46] | PASS |  |
| full_s0 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1395 | 3960 | +14.54 [+13.21, +15.79] | PASS |  |
| full_s0 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1403 | 3746 | +15.17 [+13.65, +16.58] | PASS |  |
| full_s0 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1252 | 5828 | +2.74 [+1.71, +3.77] | PASS |  |

## e3_deadline_dev_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| DL_s0_D2_iid | relay_st_s0 | cap4 | iid | deadline2 | seed901..seed964 | 128 | 1184 | 2600 | -2.78 [-3.64, -1.92] | PASS |  |
| DL_s0_D2_iid | relay_st_s0 | prefix | iid | deadline2 | seed901..seed964 | 128 | 1180 | 4906 | -3.15 [-4.08, -2.17] | PASS |  |
| DL_s0_D2_low | relay_st_s0 | prefix | low | deadline2 | seed901..seed964 | 128 | 1193 | 2403 | -2.10 [-2.94, -1.28] | PASS |  |
| DL_s0_D3_iid | relay_st_s0 | cap4 | iid | deadline3 | seed901..seed964 | 128 | 1187 | 2600 | -2.59 [-3.47, -1.67] | PASS |  |
| DL_s0_D3_iid | relay_st_s0 | prefix | iid | deadline3 | seed901..seed964 | 128 | 1178 | 4897 | -3.26 [-4.05, -2.46] | PASS |  |
| DL_s0_D3_low | relay_st_s0 | prefix | low | deadline3 | seed901..seed964 | 128 | 1193 | 2403 | -2.10 [-2.94, -1.28] | PASS |  |
| DL_s0_D4_iid | relay_st_s0 | cap4 | iid | deadline4 | seed901..seed964 | 128 | 1186 | 2600 | -2.62 [-3.40, -1.83] | PASS |  |
| DL_s0_D4_iid | relay_st_s0 | prefix | iid | deadline4 | seed901..seed964 | 128 | 1178 | 4903 | -3.29 [-4.14, -2.49] | PASS |  |
| DL_s0_D4_low | relay_st_s0 | prefix | low | deadline4 | seed901..seed964 | 128 | 1201 | 2403 | -1.41 [-2.19, -0.60] | PASS |  |
| DL_s0_D6_iid | relay_st_s0 | cap4 | iid | deadline6 | seed901..seed964 | 128 | 1189 | 2600 | -2.39 [-3.26, -1.52] | PASS |  |
| DL_s0_D6_iid | relay_st_s0 | prefix | iid | deadline6 | seed901..seed964 | 128 | 1181 | 4905 | -3.09 [-3.92, -2.22] | PASS |  |
| DL_s0_D6_low | relay_st_s0 | prefix | low | deadline6 | seed901..seed964 | 128 | 1193 | 2403 | -2.02 [-2.87, -1.16] | PASS |  |
| DL_s1_D2_iid | relay_st_s1 | cap4 | iid | deadline2 | seed901..seed964 | 128 | 1153 | 2600 | -2.69 [-3.54, -1.90] | PASS |  |
| DL_s1_D2_iid | relay_st_s1 | prefix | iid | deadline2 | seed901..seed964 | 128 | 1147 | 4910 | -3.18 [-4.02, -2.33] | PASS |  |
| DL_s1_D2_low | relay_st_s1 | prefix | low | deadline2 | seed901..seed964 | 128 | 1162 | 2394 | -1.96 [-2.90, -1.06] | PASS |  |
| DL_s1_D3_iid | relay_st_s1 | cap4 | iid | deadline3 | seed901..seed964 | 128 | 1151 | 2600 | -2.85 [-3.71, -2.02] | PASS |  |
| DL_s1_D3_iid | relay_st_s1 | prefix | iid | deadline3 | seed901..seed964 | 128 | 1146 | 4904 | -3.31 [-4.18, -2.43] | PASS |  |
| DL_s1_D3_low | relay_st_s1 | prefix | low | deadline3 | seed901..seed964 | 128 | 1162 | 2394 | -1.96 [-2.90, -1.06] | PASS |  |
| DL_s1_D4_iid | relay_st_s1 | cap4 | iid | deadline4 | seed901..seed964 | 128 | 1151 | 2600 | -2.88 [-3.62, -2.20] | PASS |  |
| DL_s1_D4_iid | relay_st_s1 | prefix | iid | deadline4 | seed901..seed964 | 128 | 1150 | 4907 | -2.97 [-3.81, -2.19] | PASS |  |
| DL_s1_D4_low | relay_st_s1 | prefix | low | deadline4 | seed901..seed964 | 128 | 1158 | 2403 | -2.26 [-3.21, -1.33] | PASS |  |
| DL_s1_D6_iid | relay_st_s1 | cap4 | iid | deadline6 | seed901..seed964 | 128 | 1155 | 2600 | -2.52 [-3.26, -1.77] | PASS |  |
| DL_s1_D6_iid | relay_st_s1 | prefix | iid | deadline6 | seed901..seed964 | 128 | 1150 | 4905 | -2.94 [-3.75, -2.14] | PASS |  |
| DL_s1_D6_low | relay_st_s1 | prefix | low | deadline6 | seed901..seed964 | 128 | 1159 | 2409 | -2.20 [-3.02, -1.38] | PASS |  |

## e3_decision_depth_20261001

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| s0_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1181 | 0 | -3.05 [-3.84, -2.19] | PASS |  |
| s0_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1184 | 0 | -2.80 [-3.70, -1.90] | PASS |  |
| s0_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1178 | 0 | -3.26 [-4.18, -2.40] | PASS |  |
| s0_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1222 | 0 | +0.35 [-0.54, +1.22] | PASS |  |
| s1_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1147 | 0 | -3.17 [-3.99, -2.39] | PASS |  |
| s1_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1150 | 0 | -2.95 [-3.90, -2.04] | PASS |  |
| s1_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1138 | 0 | -3.95 [-4.85, -3.08] | PASS |  |
| s1_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1168 | 0 | -1.39 [-2.35, -0.39] | PASS |  |

## e3_decision_depth_ten_20261001

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| cage_s0_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1206 | 0 | -1.03 [-1.92, -0.18] | PASS |  |
| cage_s1_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1162 | 0 | -1.90 [-2.82, -0.99] | PASS |  |
| cage_s2_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1167 | 0 | -4.06 [-4.87, -3.32] | PASS |  |
| cage_s3_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1215 | 0 | +0.03 [-0.88, +0.85] | PASS |  |
| cage_s4_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1186 | 0 | -1.91 [-2.67, -1.15] | PASS |  |
| cage_s5_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1208 | 0 | -0.76 [-1.60, +0.08] | PASS |  |
| cage_s6_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1242 | 0 | +0.36 [-0.39, +1.11] | PASS |  |
| cage_s7_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1128 | 0 | -2.45 [-3.23, -1.58] | PASS |  |
| cage_s8_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1263 | 0 | -0.60 [-1.35, +0.13] | PASS |  |
| cage_s9_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1235 | 0 | +0.23 [-0.49, +0.98] | PASS |  |

## e3_decision_depth_v2_20261001

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| s0_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1184 | 0 | -2.80 [-3.70, -1.90] | PASS |  |
| s1_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1150 | 0 | -2.95 [-3.90, -2.04] | PASS |  |

## e3_delivery_ceiling_20260929_181313

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| e3_delivery_ceiling_20260929_181313 | scratch_s3 | full | None | None | seed901..seed916 | 32 | 1358 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s0 | full | None | None | seed901..seed916 | 32 | 1339 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s1 | full | None | None | seed901..seed916 | 32 | 1402 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s2 | full | None | None | seed901..seed916 | 32 | 1399 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s4 | full | None | None | seed901..seed916 | 32 | 1410 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | mix_s3 | full | None | None | seed901..seed916 | 32 | 1310 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | full_s0 | full | None | None | seed901..seed916 | 32 | 1205 | 5850 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_s3 | none | None | None | seed901..seed916 | 32 | 1418 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s0 | none | None | None | seed901..seed916 | 32 | 1366 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s1 | none | None | None | seed901..seed916 | 32 | 1421 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s2 | none | None | None | seed901..seed916 | 32 | 1525 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s4 | none | None | None | seed901..seed916 | 32 | 1386 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | mix_s3 | none | None | None | seed901..seed916 | 32 | 1329 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | full_s0 | none | None | None | seed901..seed916 | 32 | 1420 | 0 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_s3 | prefix | None | None | seed901..seed916 | 32 | 1353 | 4894 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s0 | prefix | None | None | seed901..seed916 | 32 | 1322 | 4911 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s1 | prefix | None | None | seed901..seed916 | 32 | 1356 | 4908 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s2 | prefix | None | None | seed901..seed916 | 32 | 1380 | 4901 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s4 | prefix | None | None | seed901..seed916 | 32 | 1344 | 4908 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | mix_s3 | prefix | None | None | seed901..seed916 | 32 | 1341 | 4912 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | full_s0 | prefix | None | None | seed901..seed916 | 32 | 1370 | 4912 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_s3 | random | None | None | seed901..seed916 | 32 | 1366 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s0 | random | None | None | seed901..seed916 | 32 | 1348 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s1 | random | None | None | seed901..seed916 | 32 | 1440 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s2 | random | None | None | seed901..seed916 | 32 | 1412 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | scratch_rs_s4 | random | None | None | seed901..seed916 | 32 | 1409 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | mix_s3 | random | None | None | seed901..seed916 | 32 | 1350 | 4907 | — | PASS | n=32 |
| e3_delivery_ceiling_20260929_181313 | full_s0 | random | None | None | seed901..seed916 | 32 | 1396 | 4907 | — | PASS | n=32 |

## e3_fostudent_panel_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bb_set_full_s0 | set_full_s0 | prefix | iid | None | seed2201..seed2264 | 128 | 1144 | 5850 | -3.42 [-4.27, -2.55] | PASS |  |
| bb_set_full_s1 | set_full_s1 | prefix | iid | None | seed2201..seed2264 | 128 | 1115 | 5850 | -3.89 [-4.61, -3.21] | PASS |  |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2201..seed2264 | 128 | 1184 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2201..seed2264 | 128 | 1160 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2201..seed2264 | 128 | 1483 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2201..seed2264 | 128 | 1233 | 0 | +4.13 [+3.07, +5.19] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2201..seed2264 | 128 | 1224 | 0 | +5.50 [+4.54, +6.42] | PASS |  |
| st_fo_s0 | distill_fo_prefix_s0 | cap4 | iid | None | seed2201..seed2264 | 128 | 1177 | 2600 | -0.65 [-1.42, +0.12] | PASS |  |
| st_fo_s0 | distill_fo_prefix_s0 | prefix | iid | None | seed2201..seed2264 | 128 | 1175 | 4909 | -0.76 [-1.65, +0.12] | PASS |  |
| st_fo_s1 | distill_fo_prefix_s1 | cap4 | iid | None | seed2201..seed2264 | 128 | 1117 | 2600 | -3.71 [-4.49, -2.92] | PASS |  |
| st_fo_s1 | distill_fo_prefix_s1 | prefix | iid | None | seed2201..seed2264 | 128 | 1114 | 4915 | -3.98 [-4.77, -3.20] | PASS |  |

## e3_freshonly_newpanel_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| def_set_full_s0 | set_full_s0 | full | iid | None | seed2001..seed2064 | 128 | 1151 | 5850 | -2.65 [-3.49, -1.77] | PASS |  |
| def_set_full_s0 | set_full_s0 | prefix | iid | None | seed2001..seed2064 | 128 | 1233 | 4906 | +4.27 [+3.29, +5.20] | PASS |  |
| def_set_full_s1 | set_full_s1 | full | iid | None | seed2001..seed2064 | 128 | 1108 | 5850 | -3.83 [-4.55, -3.11] | PASS |  |
| def_set_full_s1 | set_full_s1 | prefix | iid | None | seed2001..seed2064 | 128 | 1219 | 4901 | +5.75 [+4.79, +6.75] | PASS |  |
| fo_set_full_s0 | set_full_s0 | cap4 | iid | None | seed2001..seed2064 | 128 | 1194 | 2600 | +1.02 [+0.15, +1.91] | PASS |  |
| fo_set_full_s0 | set_full_s0 | prefix | iid | None | seed2001..seed2064 | 128 | 1197 | 4906 | +1.26 [+0.35, +2.19] | PASS |  |
| fo_set_full_s1 | set_full_s1 | cap4 | iid | None | seed2001..seed2064 | 128 | 1158 | 2600 | +0.47 [-0.43, +1.38] | PASS |  |
| fo_set_full_s1 | set_full_s1 | prefix | iid | None | seed2001..seed2064 | 128 | 1177 | 4910 | +2.11 [+1.05, +3.23] | PASS |  |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2001..seed2064 | 128 | 1182 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2001..seed2064 | 128 | 1153 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2001..seed2064 | 128 | 1499 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2001..seed2064 | 128 | 1234 | 0 | +4.37 [+3.20, +5.49] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2001..seed2064 | 128 | 1241 | 0 | +7.69 [+6.74, +8.66] | PASS |  |
| ref_set_prefix_s0 | set_prefix_s0 | prefix | iid | None | seed2001..seed2064 | 128 | 1207 | 4906 | +2.07 [+1.02, +3.09] | PASS |  |
| ref_set_prefix_s1 | set_prefix_s1 | prefix | iid | None | seed2001..seed2064 | 128 | 1220 | 4910 | +5.83 [+4.91, +6.77] | PASS |  |

## e3_grid4x4_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| eval/distill_none_s0 | distill_none_s0 | none | iid | None | seed901..seed964 | 128 | 1303 | 0 | — | PASS |  |
| eval/set_full_s0_full | set_full_s0 | full | iid | None | seed901..seed964 | 128 | 1227 | 10400 | -5.81 [-6.71, -4.93] | PASS |  |
| eval/set_full_s0_full | set_full_s0 | prefix | iid | None | seed901..seed964 | 128 | 1511 | 9415 | +15.99 [+14.61, +17.46] | PASS |  |
| eval/set_none_s0 | set_none_s0 | none | iid | None | seed901..seed964 | 128 | 1486 | 0 | +14.08 [+12.94, +15.23] | PASS |  |

## e3_mp2_message_check_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| e3_mp2_message_check_20260929 | ? | full | None | None | seed901..seed964 | 128 | 1529 | 0 | — | None | seed? |
| e3_mp2_message_check_20260929 | ? | none | None | None | seed901..seed964 | 128 | 1529 | 0 | — | None | seed? |
| e3_mp2_message_check_20260929 | ? | prefix | None | None | seed901..seed964 | 128 | 1529 | 0 | — | None | seed? |

## e3_mp2_message_check_v2_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| e3_mp2_message_check_v2_20260929 | ? | full | None | None | seed901..seed964 | 128 | 1729 | 0 | — | None | seed? |
| e3_mp2_message_check_v2_20260929 | ? | prefix | None | None | seed901..seed964 | 128 | 1729 | 0 | — | None | seed? |

## e3_music_eval_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| relay_st_s0_agefirst_iid | relay_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1191 | 2600 | -2.26 [-3.17, -1.40] | PASS |  |
| relay_st_s0_agefirst_iid | relay_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1181 | 4902 | -3.05 [-3.84, -2.19] | PASS |  |
| relay_st_s0_agefirst_low | relay_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1184 | 2400 | -2.80 [-3.70, -1.90] | PASS |  |
| relay_st_s0_bass_iid | relay_st_s0 | cap4 | iid | bass | seed901..seed964 | 128 | 1185 | 2600 | -2.76 [-3.70, -1.85] | PASS |  |
| relay_st_s0_bass_iid | relay_st_s0 | prefix | iid | bass | seed901..seed964 | 128 | 1181 | 4902 | -3.01 [-3.92, -2.15] | PASS |  |
| relay_st_s0_bass_low | relay_st_s0 | prefix | low | bass | seed901..seed964 | 128 | 1188 | 2410 | -2.45 [-3.47, -1.48] | PASS |  |
| relay_st_s0_prefix_low | relay_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1230 | 2407 | +1.00 [+0.13, +1.85] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1136 | 2600 | -4.14 [-4.96, -3.37] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1147 | 4902 | -3.17 [-3.99, -2.39] | PASS |  |
| relay_st_s1_agefirst_low | relay_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1150 | 2400 | -2.95 [-3.90, -2.04] | PASS |  |
| relay_st_s1_bass_iid | relay_st_s1 | cap4 | iid | bass | seed901..seed964 | 128 | 1140 | 2600 | -3.80 [-4.61, -3.03] | PASS |  |
| relay_st_s1_bass_iid | relay_st_s1 | prefix | iid | bass | seed901..seed964 | 128 | 1147 | 4902 | -3.20 [-4.07, -2.39] | PASS |  |
| relay_st_s1_bass_low | relay_st_s1 | prefix | low | bass | seed901..seed964 | 128 | 1151 | 2410 | -2.88 [-3.71, -2.09] | PASS |  |
| relay_st_s1_prefix_cap4 | relay_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1169 | 2600 | -1.31 [-2.24, -0.44] | PASS |  |
| relay_st_s1_prefix_low | relay_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1170 | 2408 | -1.23 [-2.19, -0.20] | PASS |  |

## e3_ood_panel_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bb_set_full_s0 | set_full_s0 | prefix | iid | None | seed2501..seed2564 | 192 | 1456 | 5850 | -2.10 [-2.54, -1.63] | PASS | n=192 |
| bb_set_full_s1 | set_full_s1 | prefix | iid | None | seed2501..seed2564 | 192 | 1399 | 5850 | -3.23 [-3.78, -2.65] | PASS | n=192 |
| q4t_s0 | set_fullq4_s0 | prefix | iid | None | seed2501..seed2564 | 192 | 1430 | 5850 | -3.84 [-4.39, -3.31] | PASS | n=192 |
| q4t_s1 | set_fullq4_s1 | prefix | iid | None | seed2501..seed2564 | 192 | 1414 | 5850 | -2.16 [-2.75, -1.51] | PASS | n=192 |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2501..seed2564 | 192 | 1487 | 0 | — | PASS | n=192 |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2501..seed2564 | 192 | 1445 | 0 | — | PASS | n=192 |
| ref_maxq | ? | none | None | None | seed2501..seed2564 | 192 | 1845 | 0 | — | None | seed? n=192 |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2501..seed2564 | 192 | 1537 | 0 | +3.37 [+2.72, +4.02] | PASS | n=192 |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2501..seed2564 | 192 | 1533 | 0 | +6.06 [+5.31, +6.85] | PASS | n=192 |

## e3_relayrot_panel_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bb_set_full_s0 | set_full_s0 | prefix | iid | None | seed2601..seed2664 | 128 | 1141 | 5850 | -4.00 [-4.67, -3.29] | PASS |  |
| bb_set_full_s1 | set_full_s1 | prefix | iid | None | seed2601..seed2664 | 128 | 1102 | 5850 | -4.49 [-5.09, -3.90] | PASS |  |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2601..seed2664 | 128 | 1189 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2601..seed2664 | 128 | 1154 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2601..seed2664 | 128 | 1500 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2601..seed2664 | 128 | 1232 | 0 | +3.70 [+2.63, +4.79] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2601..seed2664 | 128 | 1232 | 0 | +6.73 [+5.69, +7.75] | PASS |  |
| relay_st_s0_agefirst_iid | relay_st_s0 | cap4 | iid | agefirst | seed2601..seed2664 | 128 | 1153 | 2600 | -2.96 [-3.87, -2.00] | PASS |  |
| relay_st_s0_agefirst_iid | relay_st_s0 | prefix | iid | agefirst | seed2601..seed2664 | 128 | 1163 | 4908 | -2.19 [-3.08, -1.25] | PASS |  |
| relay_st_s0_agefirst_low | relay_st_s0 | prefix | low | agefirst | seed2601..seed2664 | 128 | 1162 | 2411 | -2.19 [-2.96, -1.40] | PASS |  |
| relay_st_s0_prefix_iid | relay_st_s0 | cap4 | iid | prefix | seed2601..seed2664 | 128 | 1197 | 2600 | +0.68 [-0.11, +1.49] | PASS |  |
| relay_st_s0_prefix_iid | relay_st_s0 | prefix | iid | prefix | seed2601..seed2664 | 128 | 1156 | 4904 | -2.71 [-3.60, -1.77] | PASS |  |
| relay_st_s0_prefix_low | relay_st_s0 | prefix | low | prefix | seed2601..seed2664 | 128 | 1200 | 2405 | +0.96 [+0.10, +1.84] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | cap4 | iid | agefirst | seed2601..seed2664 | 128 | 1115 | 2600 | -3.41 [-4.08, -2.70] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | prefix | iid | agefirst | seed2601..seed2664 | 128 | 1108 | 4908 | -4.00 [-4.71, -3.29] | PASS |  |
| relay_st_s1_agefirst_low | relay_st_s1 | prefix | low | agefirst | seed2601..seed2664 | 128 | 1126 | 2411 | -2.43 [-3.17, -1.68] | PASS |  |
| relay_st_s1_prefix_iid | relay_st_s1 | cap4 | iid | prefix | seed2601..seed2664 | 128 | 1134 | 2600 | -1.76 [-2.53, -0.98] | PASS |  |
| relay_st_s1_prefix_iid | relay_st_s1 | prefix | iid | prefix | seed2601..seed2664 | 128 | 1105 | 4908 | -4.29 [-4.94, -3.65] | PASS |  |
| relay_st_s1_prefix_low | relay_st_s1 | prefix | low | prefix | seed2601..seed2664 | 128 | 1134 | 2407 | -1.74 [-2.45, -0.97] | PASS |  |

## e3_rich_dev_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| FO_s0_agefirst | set_full_s0 | prefix | rich7 | agefirst | seed901..seed964 | 128 | 1255 | 4957 | +3.04 [+2.01, +4.05] | PASS |  |
| FO_s0_prefix | set_full_s0 | prefix | rich7 | prefix | seed901..seed964 | 128 | 1275 | 4959 | +4.66 [+3.50, +5.86] | PASS |  |
| FO_s0_prefix_iid | set_full_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1217 | 4907 | -0.06 [-0.99, +0.89] | PASS |  |
| FO_s1_agefirst | set_full_s1 | prefix | rich7 | agefirst | seed901..seed964 | 128 | 1275 | 4957 | +7.60 [+6.42, +8.81] | PASS |  |
| FO_s1_prefix | set_full_s1 | prefix | rich7 | prefix | seed901..seed964 | 128 | 1290 | 4957 | +8.84 [+7.68, +9.95] | PASS |  |
| FO_s1_prefix_iid | set_full_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1210 | 4902 | +2.12 [+1.18, +3.09] | PASS |  |
| relay_s0_agefirst | relay_st_s0 | prefix | rich7 | agefirst | seed901..seed964 | 128 | 1191 | 4957 | -2.24 [-3.12, -1.40] | PASS |  |
| relay_s0_bass | relay_st_s0 | prefix | rich7 | bass | seed901..seed964 | 128 | 1184 | 4959 | -2.80 [-3.75, -1.82] | PASS |  |
| relay_s0_hub | relay_st_s0 | prefix | rich7 | hub | seed901..seed964 | 128 | 1184 | 4959 | -2.80 [-3.75, -1.82] | PASS |  |
| relay_s0_prefix | relay_st_s0 | prefix | rich7 | prefix | seed901..seed964 | 128 | 1210 | 4955 | -0.70 [-1.65, +0.25] | PASS |  |
| relay_s1_agefirst | relay_st_s1 | prefix | rich7 | agefirst | seed901..seed964 | 128 | 1154 | 4957 | -2.63 [-3.50, -1.78] | PASS |  |
| relay_s1_bass | relay_st_s1 | prefix | rich7 | bass | seed901..seed964 | 128 | 1154 | 4959 | -2.58 [-3.43, -1.78] | PASS |  |
| relay_s1_hub | relay_st_s1 | prefix | rich7 | hub | seed901..seed964 | 128 | 1154 | 4959 | -2.58 [-3.43, -1.78] | PASS |  |
| relay_s1_prefix | relay_st_s1 | prefix | rich7 | prefix | seed901..seed964 | 128 | 1188 | 4956 | +0.24 [-0.68, +1.11] | PASS |  |

## e3_satrot_eval_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| relay6A4_st_s0_agefirst_iid | relay6A4_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1182 | 2600 | -2.96 [-3.77, -2.19] | PASS |  |
| relay6A4_st_s0_agefirst_iid | relay6A4_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1180 | 4902 | -3.13 [-3.98, -2.27] | PASS |  |
| relay6A4_st_s0_agefirst_low | relay6A4_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1195 | 2400 | -1.92 [-2.82, -0.98] | PASS |  |
| relay6A4_st_s0_prefix_iid | relay6A4_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1180 | 2600 | -3.17 [-4.06, -2.29] | PASS |  |
| relay6A4_st_s0_prefix_iid | relay6A4_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1179 | 4907 | -3.23 [-4.05, -2.39] | PASS |  |
| relay6A4_st_s0_prefix_low | relay6A4_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1185 | 2404 | -2.70 [-3.53, -1.92] | PASS |  |
| relay6A4_st_s1_agefirst_iid | relay6A4_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1143 | 2600 | -3.50 [-4.41, -2.57] | PASS |  |
| relay6A4_st_s1_agefirst_iid | relay6A4_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1143 | 4902 | -3.52 [-4.29, -2.74] | PASS |  |
| relay6A4_st_s1_agefirst_low | relay6A4_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1147 | 2400 | -3.18 [-4.09, -2.33] | PASS |  |
| relay6A4_st_s1_prefix_iid | relay6A4_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1188 | 2600 | +0.31 [-0.68, +1.22] | PASS |  |
| relay6A4_st_s1_prefix_iid | relay6A4_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1144 | 4903 | -3.44 [-4.36, -2.50] | PASS |  |
| relay6A4_st_s1_prefix_low | relay6A4_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1188 | 2410 | +0.23 [-0.64, +1.09] | PASS |  |
| relay6A504_st_s0_agefirst_iid | relay6A504_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1179 | 2600 | -3.17 [-4.04, -2.22] | PASS |  |
| relay6A504_st_s0_agefirst_iid | relay6A504_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1187 | 4902 | -2.56 [-3.39, -1.69] | PASS |  |
| relay6A504_st_s0_agefirst_low | relay6A504_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1192 | 2400 | -2.13 [-3.10, -1.19] | PASS |  |
| relay6A504_st_s0_prefix_iid | relay6A504_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1223 | 2600 | +0.39 [-0.43, +1.26] | PASS |  |
| relay6A504_st_s0_prefix_iid | relay6A504_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1191 | 4907 | -2.24 [-3.02, -1.54] | PASS |  |
| relay6A504_st_s0_prefix_low | relay6A504_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1216 | 2404 | -0.13 [-1.02, +0.83] | PASS |  |
| relay6A504_st_s1_agefirst_iid | relay6A504_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1141 | 2600 | -3.67 [-4.46, -2.89] | PASS |  |
| relay6A504_st_s1_agefirst_iid | relay6A504_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1143 | 4902 | -3.55 [-4.36, -2.78] | PASS |  |
| relay6A504_st_s1_agefirst_low | relay6A504_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1154 | 2400 | -2.63 [-3.52, -1.78] | PASS |  |
| relay6A504_st_s1_prefix_iid | relay6A504_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1174 | 2600 | -0.93 [-1.78, -0.07] | PASS |  |
| relay6A504_st_s1_prefix_iid | relay6A504_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1140 | 4904 | -3.81 [-4.64, -3.00] | PASS |  |
| relay6A504_st_s1_prefix_low | relay6A504_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1170 | 2404 | -1.21 [-1.97, -0.49] | PASS |  |
| relay6B12_st_s0_agefirst_iid | relay6B12_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1173 | 2600 | -3.73 [-4.45, -2.97] | PASS |  |
| relay6B12_st_s0_agefirst_iid | relay6B12_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1174 | 4902 | -3.59 [-4.49, -2.72] | PASS |  |
| relay6B12_st_s0_agefirst_low | relay6B12_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1188 | 2400 | -2.47 [-3.39, -1.55] | PASS |  |
| relay6B12_st_s0_prefix_iid | relay6B12_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1183 | 2600 | -2.90 [-3.74, -2.06] | PASS |  |
| relay6B12_st_s0_prefix_iid | relay6B12_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1174 | 4907 | -3.62 [-4.43, -2.80] | PASS |  |
| relay6B12_st_s0_prefix_low | relay6B12_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1191 | 2409 | -2.20 [-3.04, -1.27] | PASS |  |
| relay6B12_st_s1_agefirst_iid | relay6B12_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1137 | 2600 | -4.07 [-4.88, -3.30] | PASS |  |
| relay6B12_st_s1_agefirst_iid | relay6B12_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1138 | 4902 | -3.97 [-4.86, -3.18] | PASS |  |
| relay6B12_st_s1_agefirst_low | relay6B12_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1154 | 2400 | -2.56 [-3.46, -1.66] | PASS |  |
| relay6B12_st_s1_prefix_iid | relay6B12_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1185 | 2600 | +0.05 [-0.80, +0.89] | PASS |  |
| relay6B12_st_s1_prefix_iid | relay6B12_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1137 | 4903 | -4.05 [-4.93, -3.16] | PASS |  |
| relay6B12_st_s1_prefix_low | relay6B12_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1183 | 2405 | -0.11 [-1.08, +0.81] | PASS |  |
| relay6B16_st_s0_agefirst_iid | relay6B16_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1183 | 2600 | -2.86 [-3.72, -2.00] | PASS |  |
| relay6B16_st_s0_agefirst_iid | relay6B16_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1184 | 4902 | -2.76 [-3.59, -1.89] | PASS |  |
| relay6B16_st_s0_agefirst_low | relay6B16_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1193 | 2400 | -2.07 [-2.99, -1.19] | PASS |  |
| relay6B16_st_s0_prefix_iid | relay6B16_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1206 | 2600 | -0.98 [-1.82, -0.14] | PASS |  |
| relay6B16_st_s0_prefix_iid | relay6B16_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1182 | 4909 | -2.93 [-3.72, -2.14] | PASS |  |
| relay6B16_st_s0_prefix_low | relay6B16_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1222 | 2406 | +0.31 [-0.55, +1.12] | PASS |  |
| relay6B16_st_s1_agefirst_iid | relay6B16_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1131 | 2600 | -4.52 [-5.25, -3.84] | PASS |  |
| relay6B16_st_s1_agefirst_iid | relay6B16_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1140 | 4902 | -3.77 [-4.61, -2.98] | PASS |  |
| relay6B16_st_s1_agefirst_low | relay6B16_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1143 | 2400 | -3.52 [-4.37, -2.70] | PASS |  |
| relay6B16_st_s1_prefix_iid | relay6B16_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1160 | 2600 | -2.09 [-2.82, -1.36] | PASS |  |
| relay6B16_st_s1_prefix_iid | relay6B16_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1141 | 4905 | -3.65 [-4.44, -2.84] | PASS |  |
| relay6B16_st_s1_prefix_low | relay6B16_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1159 | 2404 | -2.17 [-2.93, -1.40] | PASS |  |
| relay6B8_st_s0_agefirst_iid | relay6B8_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1193 | 2600 | -2.06 [-2.80, -1.28] | PASS |  |
| relay6B8_st_s0_agefirst_iid | relay6B8_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1191 | 4902 | -2.19 [-2.98, -1.37] | PASS |  |
| relay6B8_st_s0_agefirst_low | relay6B8_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1194 | 2400 | -1.95 [-2.79, -1.06] | PASS |  |
| relay6B8_st_s0_prefix_iid | relay6B8_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1202 | 2600 | -1.35 [-2.28, -0.39] | PASS |  |
| relay6B8_st_s0_prefix_iid | relay6B8_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1182 | 4908 | -2.94 [-3.81, -2.14] | PASS |  |
| relay6B8_st_s0_prefix_low | relay6B8_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1200 | 2408 | -1.48 [-2.34, -0.59] | PASS |  |
| relay6B8_st_s1_agefirst_iid | relay6B8_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1137 | 2600 | -4.03 [-4.79, -3.28] | PASS |  |
| relay6B8_st_s1_agefirst_iid | relay6B8_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1132 | 4902 | -4.44 [-5.20, -3.70] | PASS |  |
| relay6B8_st_s1_agefirst_low | relay6B8_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1148 | 2400 | -3.14 [-3.98, -2.33] | PASS |  |
| relay6B8_st_s1_prefix_iid | relay6B8_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1141 | 2600 | -3.71 [-4.52, -2.91] | PASS |  |
| relay6B8_st_s1_prefix_iid | relay6B8_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1136 | 4904 | -4.12 [-4.88, -3.36] | PASS |  |
| relay6B8_st_s1_prefix_low | relay6B8_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1141 | 2406 | -3.66 [-4.45, -2.88] | PASS |  |
| relay6B8_st_s3_agefirst_iid | relay6B8_st_s3 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1200 | 2600 | -1.17 [-2.02, -0.28] | PASS |  |
| relay6B8_st_s3_agefirst_iid | relay6B8_st_s3 | prefix | iid | agefirst | seed901..seed964 | 128 | 1203 | 4902 | -0.97 [-1.75, -0.19] | PASS |  |
| relay6B8_st_s3_agefirst_low | relay6B8_st_s3 | prefix | low | agefirst | seed901..seed964 | 128 | 1215 | 2400 | +0.02 [-0.85, +0.95] | PASS |  |
| relay6B8_st_s3_prefix_iid | relay6B8_st_s3 | cap4 | iid | prefix | seed901..seed964 | 128 | 1224 | 2600 | +0.77 [-0.09, +1.66] | PASS |  |
| relay6B8_st_s3_prefix_iid | relay6B8_st_s3 | prefix | iid | prefix | seed901..seed964 | 128 | 1203 | 4906 | -0.94 [-1.69, -0.18] | PASS |  |
| relay6B8_st_s3_prefix_low | relay6B8_st_s3 | prefix | low | prefix | seed901..seed964 | 128 | 1234 | 2408 | +1.57 [+0.82, +2.41] | PASS |  |
| relay6B8_st_s4_prefix_iid | relay6B8_st_s4 | cap4 | iid | prefix | seed901..seed964 | 128 | 1220 | 2599 | +0.91 [+0.05, +1.74] | PASS |  |
| relay6B8_st_s4_prefix_iid | relay6B8_st_s4 | prefix | iid | prefix | seed901..seed964 | 128 | 1182 | 4905 | -2.29 [-3.27, -1.29] | PASS |  |
| relay6B8_st_s4_prefix_low | relay6B8_st_s4 | prefix | low | prefix | seed901..seed964 | 128 | 1238 | 2407 | +2.34 [+1.44, +3.23] | PASS |  |
| relay6B8_st_s5_agefirst_iid | relay6B8_st_s5 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1208 | 2600 | -0.76 [-1.57, +0.02] | PASS |  |
| relay6B8_st_s5_agefirst_iid | relay6B8_st_s5 | prefix | iid | agefirst | seed901..seed964 | 128 | 1217 | 4902 | +0.01 [-0.88, +0.89] | PASS |  |
| relay6B8_st_s5_agefirst_low | relay6B8_st_s5 | prefix | low | agefirst | seed901..seed964 | 128 | 1205 | 2400 | -1.03 [-1.92, -0.12] | PASS |  |
| relay6B8_st_s5_prefix_iid | relay6B8_st_s5 | cap4 | iid | prefix | seed901..seed964 | 128 | 1232 | 2600 | +1.23 [+0.30, +2.22] | PASS |  |
| relay6B8_st_s5_prefix_iid | relay6B8_st_s5 | prefix | iid | prefix | seed901..seed964 | 128 | 1211 | 4903 | -0.56 [-1.42, +0.29] | PASS |  |
| relay6B8_st_s5_prefix_low | relay6B8_st_s5 | prefix | low | prefix | seed901..seed964 | 128 | 1230 | 2409 | +1.07 [+0.21, +1.93] | PASS |  |
| relay6Cage_st_s0_agefirst_iid | relay6Cage_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1186 | 2600 | -2.66 [-3.50, -1.86] | PASS |  |
| relay6Cage_st_s0_agefirst_iid | relay6Cage_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1183 | 4902 | -2.85 [-3.81, -1.84] | PASS |  |
| relay6Cage_st_s0_agefirst_low | relay6Cage_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1206 | 2400 | -1.03 [-1.92, -0.18] | PASS |  |
| relay6Cage_st_s0_prefix_iid | relay6Cage_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1246 | 2600 | +2.28 [+1.19, +3.29] | PASS |  |
| relay6Cage_st_s0_prefix_iid | relay6Cage_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1190 | 4904 | -2.28 [-3.13, -1.41] | PASS |  |
| relay6Cage_st_s0_prefix_low | relay6Cage_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1256 | 2407 | +3.15 [+2.14, +4.12] | PASS |  |
| relay6Cage_st_s1_agefirst_iid | relay6Cage_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1149 | 2600 | -3.06 [-3.99, -2.20] | PASS |  |
| relay6Cage_st_s1_agefirst_iid | relay6Cage_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1146 | 4902 | -3.25 [-4.00, -2.45] | PASS |  |
| relay6Cage_st_s1_agefirst_low | relay6Cage_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1162 | 2400 | -1.90 [-2.82, -0.99] | PASS |  |
| relay6Cage_st_s1_prefix_iid | relay6Cage_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1184 | 2600 | -0.08 [-1.00, +0.85] | PASS |  |
| relay6Cage_st_s1_prefix_iid | relay6Cage_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1150 | 4905 | -2.92 [-3.80, -2.06] | PASS |  |
| relay6Cage_st_s1_prefix_low | relay6Cage_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1187 | 2407 | +0.21 [-0.64, +1.11] | PASS |  |
| relay6Cage_st_s2_agefirst_iid | relay6Cage_st_s2 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1160 | 2600 | -4.58 [-5.49, -3.65] | PASS |  |
| relay6Cage_st_s2_agefirst_iid | relay6Cage_st_s2 | prefix | iid | agefirst | seed901..seed964 | 128 | 1169 | 4902 | -3.85 [-4.73, -2.96] | PASS |  |
| relay6Cage_st_s2_agefirst_low | relay6Cage_st_s2 | prefix | low | agefirst | seed901..seed964 | 128 | 1167 | 2400 | -4.06 [-4.87, -3.32] | PASS |  |
| relay6Cage_st_s2_prefix_iid | relay6Cage_st_s2 | cap4 | iid | prefix | seed901..seed964 | 128 | 1211 | 2600 | -0.43 [-1.43, +0.47] | PASS |  |
| relay6Cage_st_s2_prefix_iid | relay6Cage_st_s2 | prefix | iid | prefix | seed901..seed964 | 128 | 1167 | 4906 | -4.08 [-4.93, -3.20] | PASS |  |
| relay6Cage_st_s2_prefix_low | relay6Cage_st_s2 | prefix | low | prefix | seed901..seed964 | 128 | 1222 | 2406 | +0.49 [-0.49, +1.46] | PASS |  |
| relay6Cage_st_s3_agefirst_iid | relay6Cage_st_s3 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1203 | 2600 | -0.96 [-1.83, -0.08] | PASS |  |
| relay6Cage_st_s3_agefirst_iid | relay6Cage_st_s3 | prefix | iid | agefirst | seed901..seed964 | 128 | 1203 | 4902 | -0.99 [-1.80, -0.20] | PASS |  |
| relay6Cage_st_s3_agefirst_low | relay6Cage_st_s3 | prefix | low | agefirst | seed901..seed964 | 128 | 1215 | 2400 | +0.03 [-0.88, +0.85] | PASS |  |
| relay6Cage_st_s3_prefix_iid | relay6Cage_st_s3 | cap4 | iid | prefix | seed901..seed964 | 128 | 1228 | 2600 | +1.07 [+0.18, +1.93] | PASS |  |
| relay6Cage_st_s3_prefix_iid | relay6Cage_st_s3 | prefix | iid | prefix | seed901..seed964 | 128 | 1203 | 4908 | -0.98 [-1.87, -0.08] | PASS |  |
| relay6Cage_st_s3_prefix_low | relay6Cage_st_s3 | prefix | low | prefix | seed901..seed964 | 128 | 1232 | 2407 | +1.42 [+0.52, +2.32] | PASS |  |
| relay6Cage_st_s4_agefirst_iid | relay6Cage_st_s4 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1170 | 2600 | -3.23 [-4.01, -2.41] | PASS |  |
| relay6Cage_st_s4_agefirst_iid | relay6Cage_st_s4 | prefix | iid | agefirst | seed901..seed964 | 128 | 1172 | 4902 | -3.07 [-3.96, -2.12] | PASS |  |
| relay6Cage_st_s4_agefirst_low | relay6Cage_st_s4 | prefix | low | agefirst | seed901..seed964 | 128 | 1186 | 2400 | -1.91 [-2.67, -1.15] | PASS |  |
| relay6Cage_st_s4_prefix_iid | relay6Cage_st_s4 | cap4 | iid | prefix | seed901..seed964 | 128 | 1192 | 2600 | -1.44 [-2.30, -0.57] | PASS |  |
| relay6Cage_st_s4_prefix_iid | relay6Cage_st_s4 | prefix | iid | prefix | seed901..seed964 | 128 | 1180 | 4905 | -2.40 [-3.22, -1.58] | PASS |  |
| relay6Cage_st_s4_prefix_low | relay6Cage_st_s4 | prefix | low | prefix | seed901..seed964 | 128 | 1195 | 2409 | -1.15 [-2.20, -0.10] | PASS |  |
| relay6Cage_st_s5_agefirst_iid | relay6Cage_st_s5 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1206 | 2600 | -0.94 [-1.78, -0.07] | PASS |  |
| relay6Cage_st_s5_agefirst_iid | relay6Cage_st_s5 | prefix | iid | agefirst | seed901..seed964 | 128 | 1208 | 4902 | -0.80 [-1.59, +0.05] | PASS |  |
| relay6Cage_st_s5_agefirst_low | relay6Cage_st_s5 | prefix | low | agefirst | seed901..seed964 | 128 | 1208 | 2400 | -0.76 [-1.60, +0.08] | PASS |  |
| relay6Cage_st_s5_prefix_iid | relay6Cage_st_s5 | cap4 | iid | prefix | seed901..seed964 | 128 | 1225 | 2600 | +0.63 [-0.27, +1.48] | PASS |  |
| relay6Cage_st_s5_prefix_iid | relay6Cage_st_s5 | prefix | iid | prefix | seed901..seed964 | 128 | 1221 | 4902 | +0.30 [-0.63, +1.25] | PASS |  |
| relay6Cage_st_s5_prefix_low | relay6Cage_st_s5 | prefix | low | prefix | seed901..seed964 | 128 | 1228 | 2407 | +0.91 [-0.04, +1.87] | PASS |  |
| relay6Cage_st_s6_agefirst_iid | relay6Cage_st_s6 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1233 | 2600 | -0.44 [-1.08, +0.25] | PASS |  |
| relay6Cage_st_s6_agefirst_iid | relay6Cage_st_s6 | prefix | iid | agefirst | seed901..seed964 | 128 | 1219 | 4902 | -1.55 [-2.35, -0.74] | PASS |  |
| relay6Cage_st_s6_agefirst_low | relay6Cage_st_s6 | prefix | low | agefirst | seed901..seed964 | 128 | 1242 | 2400 | +0.36 [-0.39, +1.11] | PASS |  |
| relay6Cage_st_s6_prefix_iid | relay6Cage_st_s6 | cap4 | iid | prefix | seed901..seed964 | 128 | 1254 | 2600 | +1.31 [+0.55, +2.13] | PASS |  |
| relay6Cage_st_s6_prefix_iid | relay6Cage_st_s6 | prefix | iid | prefix | seed901..seed964 | 128 | 1235 | 4904 | -0.23 [-1.11, +0.63] | PASS |  |
| relay6Cage_st_s6_prefix_low | relay6Cage_st_s6 | prefix | low | prefix | seed901..seed964 | 128 | 1258 | 2410 | +1.62 [+0.79, +2.51] | PASS |  |
| relay6Cage_st_s7_agefirst_iid | relay6Cage_st_s7 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1121 | 2600 | -3.00 [-3.77, -2.23] | PASS |  |
| relay6Cage_st_s7_agefirst_iid | relay6Cage_st_s7 | prefix | iid | agefirst | seed901..seed964 | 128 | 1120 | 4902 | -3.09 [-3.79, -2.36] | PASS |  |
| relay6Cage_st_s7_agefirst_low | relay6Cage_st_s7 | prefix | low | agefirst | seed901..seed964 | 128 | 1128 | 2400 | -2.45 [-3.23, -1.58] | PASS |  |
| relay6Cage_st_s7_prefix_iid | relay6Cage_st_s7 | cap4 | iid | prefix | seed901..seed964 | 128 | 1130 | 2600 | -2.27 [-3.05, -1.47] | PASS |  |
| relay6Cage_st_s7_prefix_iid | relay6Cage_st_s7 | prefix | iid | prefix | seed901..seed964 | 128 | 1116 | 4906 | -3.43 [-4.14, -2.68] | PASS |  |
| relay6Cage_st_s7_prefix_low | relay6Cage_st_s7 | prefix | low | prefix | seed901..seed964 | 128 | 1139 | 2408 | -1.45 [-2.40, -0.50] | PASS |  |
| relay6Cage_st_s8_agefirst_iid | relay6Cage_st_s8 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1255 | 2600 | -1.26 [-2.12, -0.41] | PASS |  |
| relay6Cage_st_s8_agefirst_iid | relay6Cage_st_s8 | prefix | iid | agefirst | seed901..seed964 | 128 | 1257 | 4902 | -1.12 [-1.86, -0.34] | PASS |  |
| relay6Cage_st_s8_agefirst_low | relay6Cage_st_s8 | prefix | low | agefirst | seed901..seed964 | 128 | 1263 | 2400 | -0.60 [-1.35, +0.13] | PASS |  |
| relay6Cage_st_s8_prefix_iid | relay6Cage_st_s8 | cap4 | iid | prefix | seed901..seed964 | 128 | 1272 | 2600 | +0.05 [-0.71, +0.84] | PASS |  |
| relay6Cage_st_s8_prefix_iid | relay6Cage_st_s8 | prefix | iid | prefix | seed901..seed964 | 128 | 1261 | 4902 | -0.77 [-1.58, +0.07] | PASS |  |
| relay6Cage_st_s8_prefix_low | relay6Cage_st_s8 | prefix | low | prefix | seed901..seed964 | 128 | 1282 | 2406 | +0.90 [+0.13, +1.71] | PASS |  |
| relay6Cage_st_s9_agefirst_iid | relay6Cage_st_s9 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1227 | 2600 | -0.44 [-1.21, +0.31] | PASS |  |
| relay6Cage_st_s9_agefirst_iid | relay6Cage_st_s9 | prefix | iid | agefirst | seed901..seed964 | 128 | 1231 | 4902 | -0.13 [-0.87, +0.65] | PASS |  |
| relay6Cage_st_s9_agefirst_low | relay6Cage_st_s9 | prefix | low | agefirst | seed901..seed964 | 128 | 1235 | 2400 | +0.23 [-0.49, +0.98] | PASS |  |
| relay6Cage_st_s9_prefix_iid | relay6Cage_st_s9 | cap4 | iid | prefix | seed901..seed964 | 128 | 1236 | 2600 | +0.24 [-0.55, +1.08] | PASS |  |
| relay6Cage_st_s9_prefix_iid | relay6Cage_st_s9 | prefix | iid | prefix | seed901..seed964 | 128 | 1223 | 4905 | -0.76 [-1.46, -0.00] | PASS |  |
| relay6Cage_st_s9_prefix_low | relay6Cage_st_s9 | prefix | low | prefix | seed901..seed964 | 128 | 1239 | 2410 | +0.52 [-0.22, +1.36] | PASS |  |
| relay6Clow_st_s0_agefirst_iid | relay6Clow_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1196 | 2600 | -1.83 [-2.72, -0.97] | PASS |  |
| relay6Clow_st_s0_agefirst_iid | relay6Clow_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1200 | 4902 | -1.50 [-2.41, -0.55] | PASS |  |
| relay6Clow_st_s0_agefirst_low | relay6Clow_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1215 | 2400 | -0.27 [-1.19, +0.71] | PASS |  |
| relay6Clow_st_s0_prefix_iid | relay6Clow_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1177 | 2600 | -3.36 [-4.19, -2.50] | PASS |  |
| relay6Clow_st_s0_prefix_iid | relay6Clow_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1186 | 4906 | -2.61 [-3.36, -1.85] | PASS |  |
| relay6Clow_st_s0_prefix_low | relay6Clow_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1182 | 2409 | -2.94 [-3.77, -2.04] | PASS |  |
| relay6Clow_st_s1_agefirst_iid | relay6Clow_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1172 | 2600 | -1.07 [-1.96, -0.21] | PASS |  |
| relay6Clow_st_s1_agefirst_iid | relay6Clow_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1169 | 4902 | -1.34 [-2.15, -0.57] | PASS |  |
| relay6Clow_st_s1_agefirst_low | relay6Clow_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1179 | 2400 | -0.51 [-1.35, +0.32] | PASS |  |
| relay6Clow_st_s1_prefix_iid | relay6Clow_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1138 | 2600 | -3.96 [-4.70, -3.25] | PASS |  |
| relay6Clow_st_s1_prefix_iid | relay6Clow_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1165 | 4904 | -1.64 [-2.56, -0.77] | PASS |  |
| relay6Clow_st_s1_prefix_low | relay6Clow_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1135 | 2408 | -4.19 [-4.91, -3.44] | PASS |  |
| relay6_st_s0_agefirst_iid | relay6_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1185 | 2600 | -2.75 [-3.67, -1.89] | PASS |  |
| relay6_st_s0_agefirst_iid | relay6_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1185 | 4902 | -2.72 [-3.57, -1.89] | PASS |  |
| relay6_st_s0_agefirst_low | relay6_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1193 | 2400 | -2.05 [-2.93, -1.17] | PASS |  |
| relay6_st_s0_prefix_iid | relay6_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1212 | 2600 | -0.47 [-1.34, +0.36] | PASS |  |
| relay6_st_s0_prefix_iid | relay6_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1187 | 4905 | -2.59 [-3.46, -1.72] | PASS |  |
| relay6_st_s0_prefix_low | relay6_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1221 | 2406 | +0.27 [-0.55, +1.16] | PASS |  |
| relay6_st_s1_agefirst_iid | relay6_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1158 | 2600 | -2.27 [-3.06, -1.44] | PASS |  |
| relay6_st_s1_agefirst_iid | relay6_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1149 | 4902 | -3.00 [-3.83, -2.17] | PASS |  |
| relay6_st_s1_agefirst_low | relay6_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1159 | 2400 | -2.22 [-3.08, -1.42] | PASS |  |
| relay6_st_s1_prefix_iid | relay6_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1190 | 2600 | +0.44 [-0.44, +1.35] | PASS |  |
| relay6_st_s1_prefix_iid | relay6_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1138 | 4904 | -3.96 [-4.77, -3.18] | PASS |  |
| relay6_st_s1_prefix_low | relay6_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1196 | 2407 | +0.97 [+0.04, +1.83] | PASS |  |
| relay6_st_s2_agefirst_iid | relay6_st_s2 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1156 | 2600 | -4.97 [-5.80, -4.17] | PASS |  |
| relay6_st_s2_agefirst_iid | relay6_st_s2 | prefix | iid | agefirst | seed901..seed964 | 128 | 1156 | 4902 | -4.96 [-5.93, -4.03] | PASS |  |
| relay6_st_s2_agefirst_low | relay6_st_s2 | prefix | low | agefirst | seed901..seed964 | 128 | 1156 | 2400 | -4.92 [-5.93, -3.98] | PASS |  |
| relay6_st_s2_prefix_iid | relay6_st_s2 | cap4 | iid | prefix | seed901..seed964 | 128 | 1185 | 2600 | -2.54 [-3.41, -1.68] | PASS |  |
| relay6_st_s2_prefix_iid | relay6_st_s2 | prefix | iid | prefix | seed901..seed964 | 128 | 1159 | 4903 | -4.70 [-5.56, -3.85] | PASS |  |
| relay6_st_s2_prefix_low | relay6_st_s2 | prefix | low | prefix | seed901..seed964 | 128 | 1185 | 2408 | -2.56 [-3.42, -1.71] | PASS |  |
| relay6_st_s3_agefirst_iid | relay6_st_s3 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1214 | 2600 | -0.02 [-0.88, +0.88] | PASS |  |
| relay6_st_s3_agefirst_iid | relay6_st_s3 | prefix | iid | agefirst | seed901..seed964 | 128 | 1209 | 4902 | -0.46 [-1.30, +0.45] | PASS |  |
| relay6_st_s3_agefirst_low | relay6_st_s3 | prefix | low | agefirst | seed901..seed964 | 128 | 1216 | 2400 | +0.11 [-0.77, +0.97] | PASS |  |
| relay6_st_s3_prefix_iid | relay6_st_s3 | cap4 | iid | prefix | seed901..seed964 | 128 | 1225 | 2600 | +0.86 [-0.01, +1.75] | PASS |  |
| relay6_st_s3_prefix_iid | relay6_st_s3 | prefix | iid | prefix | seed901..seed964 | 128 | 1204 | 4910 | -0.90 [-1.69, -0.09] | PASS |  |
| relay6_st_s3_prefix_low | relay6_st_s3 | prefix | low | prefix | seed901..seed964 | 128 | 1222 | 2408 | +0.58 [-0.40, +1.57] | PASS |  |
| relay6_st_s4_agefirst_iid | relay6_st_s4 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1180 | 2600 | -2.41 [-3.23, -1.53] | PASS |  |
| relay6_st_s4_agefirst_iid | relay6_st_s4 | prefix | iid | agefirst | seed901..seed964 | 128 | 1183 | 4902 | -2.17 [-3.07, -1.24] | PASS |  |
| relay6_st_s4_agefirst_low | relay6_st_s4 | prefix | low | agefirst | seed901..seed964 | 128 | 1200 | 2400 | -0.76 [-1.67, +0.20] | PASS |  |
| relay6_st_s4_prefix_iid | relay6_st_s4 | cap4 | iid | prefix | seed901..seed964 | 128 | 1202 | 2600 | -0.66 [-1.58, +0.20] | PASS |  |
| relay6_st_s4_prefix_iid | relay6_st_s4 | prefix | iid | prefix | seed901..seed964 | 128 | 1187 | 4906 | -1.86 [-2.75, -0.94] | PASS |  |
| relay6_st_s4_prefix_low | relay6_st_s4 | prefix | low | prefix | seed901..seed964 | 128 | 1220 | 2407 | +0.89 [-0.11, +1.91] | PASS |  |
| relay6_st_s5_agefirst_iid | relay6_st_s5 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1214 | 2600 | -0.26 [-1.12, +0.68] | PASS |  |
| relay6_st_s5_agefirst_iid | relay6_st_s5 | prefix | iid | agefirst | seed901..seed964 | 128 | 1212 | 4902 | -0.41 [-1.35, +0.55] | PASS |  |
| relay6_st_s5_agefirst_low | relay6_st_s5 | prefix | low | agefirst | seed901..seed964 | 128 | 1209 | 2400 | -0.68 [-1.63, +0.35] | PASS |  |
| relay6_st_s5_prefix_iid | relay6_st_s5 | cap4 | iid | prefix | seed901..seed964 | 128 | 1226 | 2600 | +0.67 [-0.32, +1.64] | PASS |  |
| relay6_st_s5_prefix_iid | relay6_st_s5 | prefix | iid | prefix | seed901..seed964 | 128 | 1211 | 4904 | -0.52 [-1.53, +0.44] | PASS |  |
| relay6_st_s5_prefix_low | relay6_st_s5 | prefix | low | prefix | seed901..seed964 | 128 | 1226 | 2408 | +0.74 [-0.14, +1.65] | PASS |  |
| relay6_st_s6_agefirst_iid | relay6_st_s6 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1219 | 2600 | -1.51 [-2.22, -0.78] | PASS |  |
| relay6_st_s6_agefirst_iid | relay6_st_s6 | prefix | iid | agefirst | seed901..seed964 | 128 | 1215 | 4902 | -1.89 [-2.62, -1.06] | PASS |  |
| relay6_st_s6_agefirst_low | relay6_st_s6 | prefix | low | agefirst | seed901..seed964 | 128 | 1226 | 2400 | -0.95 [-1.75, -0.16] | PASS |  |
| relay6_st_s6_prefix_iid | relay6_st_s6 | cap4 | iid | prefix | seed901..seed964 | 128 | 1289 | 2600 | +4.09 [+3.35, +4.85] | PASS |  |
| relay6_st_s6_prefix_iid | relay6_st_s6 | prefix | iid | prefix | seed901..seed964 | 128 | 1220 | 4905 | -1.49 [-2.18, -0.76] | PASS |  |
| relay6_st_s6_prefix_low | relay6_st_s6 | prefix | low | prefix | seed901..seed964 | 128 | 1290 | 2406 | +4.22 [+3.39, +5.04] | PASS |  |
| relay6_st_s7_agefirst_iid | relay6_st_s7 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1124 | 2600 | -2.76 [-3.42, -2.07] | PASS |  |
| relay6_st_s7_agefirst_iid | relay6_st_s7 | prefix | iid | agefirst | seed901..seed964 | 128 | 1130 | 4902 | -2.26 [-3.02, -1.47] | PASS |  |
| relay6_st_s7_agefirst_low | relay6_st_s7 | prefix | low | agefirst | seed901..seed964 | 128 | 1127 | 2400 | -2.47 [-3.18, -1.75] | PASS |  |
| relay6_st_s7_prefix_iid | relay6_st_s7 | cap4 | iid | prefix | seed901..seed964 | 128 | 1132 | 2600 | -2.07 [-2.89, -1.21] | PASS |  |
| relay6_st_s7_prefix_iid | relay6_st_s7 | prefix | iid | prefix | seed901..seed964 | 128 | 1122 | 4907 | -2.96 [-3.60, -2.29] | PASS |  |
| relay6_st_s7_prefix_low | relay6_st_s7 | prefix | low | prefix | seed901..seed964 | 128 | 1134 | 2412 | -1.88 [-2.75, -0.95] | PASS |  |
| relay6_st_s8_agefirst_iid | relay6_st_s8 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1254 | 2600 | -1.33 [-2.13, -0.51] | PASS |  |
| relay6_st_s8_agefirst_iid | relay6_st_s8 | prefix | iid | agefirst | seed901..seed964 | 128 | 1251 | 4902 | -1.58 [-2.33, -0.83] | PASS |  |
| relay6_st_s8_agefirst_low | relay6_st_s8 | prefix | low | agefirst | seed901..seed964 | 128 | 1255 | 2400 | -1.26 [-2.04, -0.46] | PASS |  |
| relay6_st_s8_prefix_iid | relay6_st_s8 | cap4 | iid | prefix | seed901..seed964 | 128 | 1262 | 2600 | -0.72 [-1.46, +0.05] | PASS |  |
| relay6_st_s8_prefix_iid | relay6_st_s8 | prefix | iid | prefix | seed901..seed964 | 128 | 1254 | 4901 | -1.30 [-2.01, -0.50] | PASS |  |
| relay6_st_s8_prefix_low | relay6_st_s8 | prefix | low | prefix | seed901..seed964 | 128 | 1261 | 2407 | -0.81 [-1.48, -0.04] | PASS |  |
| relay6_st_s9_agefirst_iid | relay6_st_s9 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1241 | 2600 | +0.64 [-0.17, +1.49] | PASS |  |
| relay6_st_s9_agefirst_iid | relay6_st_s9 | prefix | iid | agefirst | seed901..seed964 | 128 | 1242 | 4902 | +0.76 [-0.02, +1.58] | PASS |  |
| relay6_st_s9_agefirst_low | relay6_st_s9 | prefix | low | agefirst | seed901..seed964 | 128 | 1241 | 2400 | +0.66 [-0.09, +1.39] | PASS |  |
| relay6_st_s9_prefix_iid | relay6_st_s9 | cap4 | iid | prefix | seed901..seed964 | 128 | 1245 | 2599 | +1.04 [+0.14, +1.95] | PASS |  |
| relay6_st_s9_prefix_iid | relay6_st_s9 | prefix | iid | prefix | seed901..seed964 | 128 | 1237 | 4906 | +0.36 [-0.27, +0.98] | PASS |  |
| relay6_st_s9_prefix_low | relay6_st_s9 | prefix | low | prefix | seed901..seed964 | 128 | 1253 | 2408 | +1.62 [+0.74, +2.48] | PASS |  |
| relay_st_s0_agefirst_iid | relay_st_s0 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1191 | 2600 | -2.26 [-3.17, -1.40] | PASS |  |
| relay_st_s0_agefirst_iid | relay_st_s0 | prefix | iid | agefirst | seed901..seed964 | 128 | 1181 | 4902 | -3.05 [-3.84, -2.19] | PASS |  |
| relay_st_s0_agefirst_low | relay_st_s0 | prefix | low | agefirst | seed901..seed964 | 128 | 1184 | 2400 | -2.80 [-3.70, -1.90] | PASS |  |
| relay_st_s0_prefix_iid | relay_st_s0 | cap4 | iid | prefix | seed901..seed964 | 128 | 1230 | 2600 | +0.94 [+0.01, +1.89] | PASS |  |
| relay_st_s0_prefix_iid | relay_st_s0 | prefix | iid | prefix | seed901..seed964 | 128 | 1178 | 4902 | -3.26 [-4.18, -2.40] | PASS |  |
| relay_st_s0_prefix_low | relay_st_s0 | prefix | low | prefix | seed901..seed964 | 128 | 1222 | 2409 | +0.35 [-0.54, +1.22] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | cap4 | iid | agefirst | seed901..seed964 | 128 | 1136 | 2600 | -4.14 [-4.96, -3.37] | PASS |  |
| relay_st_s1_agefirst_iid | relay_st_s1 | prefix | iid | agefirst | seed901..seed964 | 128 | 1147 | 4902 | -3.17 [-3.99, -2.39] | PASS |  |
| relay_st_s1_agefirst_low | relay_st_s1 | prefix | low | agefirst | seed901..seed964 | 128 | 1150 | 2400 | -2.95 [-3.90, -2.04] | PASS |  |
| relay_st_s1_prefix_iid | relay_st_s1 | cap4 | iid | prefix | seed901..seed964 | 128 | 1166 | 2600 | -1.61 [-2.58, -0.70] | PASS |  |
| relay_st_s1_prefix_iid | relay_st_s1 | prefix | iid | prefix | seed901..seed964 | 128 | 1138 | 4902 | -3.95 [-4.85, -3.08] | PASS |  |
| relay_st_s1_prefix_low | relay_st_s1 | prefix | low | prefix | seed901..seed964 | 128 | 1168 | 2409 | -1.39 [-2.35, -0.39] | PASS |  |

## e3_setfresh_panel_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2301..seed2364 | 128 | 1188 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2301..seed2364 | 128 | 1163 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2301..seed2364 | 128 | 1512 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2301..seed2364 | 128 | 1236 | 0 | +4.12 [+3.31, +4.90] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2301..seed2364 | 128 | 1235 | 0 | +6.19 [+5.14, +7.23] | PASS |  |
| ref_set_prefix_s0 | set_prefix_s0 | prefix | iid | None | seed2301..seed2364 | 128 | 1206 | 4896 | +1.59 [+0.75, +2.39] | PASS |  |
| ref_set_prefix_s1 | set_prefix_s1 | prefix | iid | None | seed2301..seed2364 | 128 | 1218 | 4896 | +4.74 [+3.61, +5.84] | PASS |  |
| sf_s0 | set_fresh_s0 | cap4 | iid | None | seed2301..seed2364 | 128 | 1171 | 2600 | -1.39 [-2.37, -0.41] | PASS |  |
| sf_s0 | set_fresh_s0 | prefix | iid | None | seed2301..seed2364 | 128 | 1164 | 4895 | -2.00 [-2.90, -1.04] | PASS |  |
| sf_s1 | set_fresh_s1 | cap4 | iid | None | seed2301..seed2364 | 128 | 1263 | 2600 | +8.61 [+7.58, +9.67] | PASS |  |
| sf_s1 | set_fresh_s1 | prefix | iid | None | seed2301..seed2364 | 128 | 1246 | 4894 | +7.20 [+6.17, +8.23] | PASS |  |
| st_fo_s0 | distill_fo_prefix_s0 | prefix | iid | None | seed2301..seed2364 | 128 | 1169 | 4894 | -1.54 [-2.25, -0.75] | PASS |  |
| st_fo_s1 | distill_fo_prefix_s1 | prefix | iid | None | seed2301..seed2364 | 128 | 1115 | 4891 | -4.06 [-4.84, -3.33] | PASS |  |

## e3_ten_seed_panel_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| C_s0_agefirst_iid | relay6Cage_st_s0 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1172 | 2600 | -1.48 [-2.25, -0.73] | PASS |  |
| C_s0_agefirst_iid | relay6Cage_st_s0 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1160 | 4913 | -2.48 [-3.30, -1.64] | PASS |  |
| C_s0_agefirst_low | relay6Cage_st_s0 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1180 | 2401 | -0.79 [-1.59, -0.01] | PASS |  |
| C_s0_prefix_iid | relay6Cage_st_s0 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1224 | 2600 | +2.85 [+1.88, +3.78] | PASS |  |
| C_s0_prefix_iid | relay6Cage_st_s0 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1172 | 4915 | -1.47 [-2.49, -0.49] | PASS |  |
| C_s0_prefix_low | relay6Cage_st_s0 | prefix | low | prefix | seed2701..seed2764 | 128 | 1230 | 2409 | +3.39 [+2.46, +4.38] | PASS |  |
| C_s1_agefirst_iid | relay6Cage_st_s1 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1114 | 2600 | -3.57 [-4.51, -2.67] | PASS |  |
| C_s1_agefirst_iid | relay6Cage_st_s1 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1115 | 4913 | -3.47 [-4.38, -2.62] | PASS |  |
| C_s1_agefirst_low | relay6Cage_st_s1 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1131 | 2401 | -2.08 [-2.80, -1.33] | PASS |  |
| C_s1_prefix_iid | relay6Cage_st_s1 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1144 | 2600 | -0.93 [-1.74, -0.10] | PASS |  |
| C_s1_prefix_iid | relay6Cage_st_s1 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1116 | 4918 | -3.39 [-4.26, -2.62] | PASS |  |
| C_s1_prefix_low | relay6Cage_st_s1 | prefix | low | prefix | seed2701..seed2764 | 128 | 1151 | 2407 | -0.37 [-1.19, +0.49] | PASS |  |
| C_s2_agefirst_iid | relay6Cage_st_s2 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1127 | 2600 | -5.02 [-5.94, -4.13] | PASS |  |
| C_s2_agefirst_iid | relay6Cage_st_s2 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1126 | 4913 | -5.09 [-5.98, -4.22] | PASS |  |
| C_s2_agefirst_low | relay6Cage_st_s2 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1142 | 2401 | -3.80 [-4.67, -2.89] | PASS |  |
| C_s2_prefix_iid | relay6Cage_st_s2 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1194 | 2600 | +0.57 [-0.34, +1.46] | PASS |  |
| C_s2_prefix_iid | relay6Cage_st_s2 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1132 | 4916 | -4.61 [-5.34, -3.87] | PASS |  |
| C_s2_prefix_low | relay6Cage_st_s2 | prefix | low | prefix | seed2701..seed2764 | 128 | 1191 | 2409 | +0.38 [-0.59, +1.34] | PASS |  |
| C_s3_agefirst_iid | relay6Cage_st_s3 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1169 | 2600 | -2.05 [-2.78, -1.37] | PASS |  |
| C_s3_agefirst_iid | relay6Cage_st_s3 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1170 | 4913 | -1.97 [-2.77, -1.15] | PASS |  |
| C_s3_agefirst_low | relay6Cage_st_s3 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1185 | 2401 | -0.66 [-1.50, +0.15] | PASS |  |
| C_s3_prefix_iid | relay6Cage_st_s3 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1199 | 2600 | +0.50 [-0.31, +1.29] | PASS |  |
| C_s3_prefix_iid | relay6Cage_st_s3 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1172 | 4918 | -1.82 [-2.73, -0.90] | PASS |  |
| C_s3_prefix_low | relay6Cage_st_s3 | prefix | low | prefix | seed2701..seed2764 | 128 | 1206 | 2412 | +1.04 [+0.27, +1.83] | PASS |  |
| C_s4_agefirst_iid | relay6Cage_st_s4 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1149 | 2600 | -3.54 [-4.33, -2.72] | PASS |  |
| C_s4_agefirst_iid | relay6Cage_st_s4 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1142 | 4913 | -4.12 [-4.88, -3.29] | PASS |  |
| C_s4_agefirst_low | relay6Cage_st_s4 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1163 | 2401 | -2.37 [-3.07, -1.65] | PASS |  |
| C_s4_prefix_iid | relay6Cage_st_s4 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1165 | 2600 | -2.16 [-2.93, -1.40] | PASS |  |
| C_s4_prefix_iid | relay6Cage_st_s4 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1156 | 4916 | -2.90 [-3.60, -2.16] | PASS |  |
| C_s4_prefix_low | relay6Cage_st_s4 | prefix | low | prefix | seed2701..seed2764 | 128 | 1163 | 2410 | -2.30 [-3.05, -1.49] | PASS |  |
| C_s5_agefirst_iid | relay6Cage_st_s5 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1189 | 2600 | +0.22 [-0.54, +0.99] | PASS |  |
| C_s5_agefirst_iid | relay6Cage_st_s5 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1178 | 4913 | -0.78 [-1.71, +0.22] | PASS |  |
| C_s5_agefirst_low | relay6Cage_st_s5 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1187 | 2401 | +0.05 [-0.82, +0.90] | PASS |  |
| C_s5_prefix_iid | relay6Cage_st_s5 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1198 | 2600 | +0.91 [+0.05, +1.68] | PASS |  |
| C_s5_prefix_iid | relay6Cage_st_s5 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1181 | 4915 | -0.50 [-1.37, +0.36] | PASS |  |
| C_s5_prefix_low | relay6Cage_st_s5 | prefix | low | prefix | seed2701..seed2764 | 128 | 1196 | 2406 | +0.78 [-0.13, +1.68] | PASS |  |
| C_s6_agefirst_iid | relay6Cage_st_s6 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1207 | 2600 | -0.66 [-1.57, +0.34] | PASS |  |
| C_s6_agefirst_iid | relay6Cage_st_s6 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1205 | 4913 | -0.81 [-1.60, +0.02] | PASS |  |
| C_s6_agefirst_low | relay6Cage_st_s6 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1217 | 2401 | +0.14 [-0.65, +0.94] | PASS |  |
| C_s6_prefix_iid | relay6Cage_st_s6 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1227 | 2600 | +1.01 [+0.05, +1.92] | PASS |  |
| C_s6_prefix_iid | relay6Cage_st_s6 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1206 | 4919 | -0.76 [-1.59, +0.15] | PASS |  |
| C_s6_prefix_low | relay6Cage_st_s6 | prefix | low | prefix | seed2701..seed2764 | 128 | 1233 | 2410 | +1.52 [+0.62, +2.44] | PASS |  |
| C_s7_agefirst_iid | relay6Cage_st_s7 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1099 | 2600 | -2.31 [-3.06, -1.56] | PASS |  |
| C_s7_agefirst_iid | relay6Cage_st_s7 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1098 | 4913 | -2.40 [-3.03, -1.79] | PASS |  |
| C_s7_agefirst_low | relay6Cage_st_s7 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1102 | 2401 | -2.11 [-2.85, -1.41] | PASS |  |
| C_s7_prefix_iid | relay6Cage_st_s7 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1099 | 2600 | -2.38 [-3.20, -1.53] | PASS |  |
| C_s7_prefix_iid | relay6Cage_st_s7 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1096 | 4915 | -2.64 [-3.40, -1.94] | PASS |  |
| C_s7_prefix_low | relay6Cage_st_s7 | prefix | low | prefix | seed2701..seed2764 | 128 | 1108 | 2407 | -1.53 [-2.28, -0.81] | PASS |  |
| C_s8_agefirst_iid | relay6Cage_st_s8 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1237 | 2600 | -0.56 [-1.29, +0.19] | PASS |  |
| C_s8_agefirst_iid | relay6Cage_st_s8 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1237 | 4913 | -0.56 [-1.24, +0.20] | PASS |  |
| C_s8_agefirst_low | relay6Cage_st_s8 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1244 | 2401 | +0.05 [-0.73, +0.82] | PASS |  |
| C_s8_prefix_iid | relay6Cage_st_s8 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1251 | 2600 | +0.54 [-0.26, +1.37] | PASS |  |
| C_s8_prefix_iid | relay6Cage_st_s8 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1241 | 4917 | -0.25 [-1.02, +0.53] | PASS |  |
| C_s8_prefix_low | relay6Cage_st_s8 | prefix | low | prefix | seed2701..seed2764 | 128 | 1256 | 2412 | +0.99 [+0.18, +1.80] | PASS |  |
| C_s9_agefirst_iid | relay6Cage_st_s9 | cap4 | iid | agefirst | seed2701..seed2764 | 128 | 1194 | 2600 | -1.39 [-2.10, -0.67] | PASS |  |
| C_s9_agefirst_iid | relay6Cage_st_s9 | prefix | iid | agefirst | seed2701..seed2764 | 128 | 1196 | 4913 | -1.20 [-2.12, -0.28] | PASS |  |
| C_s9_agefirst_low | relay6Cage_st_s9 | prefix | low | agefirst | seed2701..seed2764 | 128 | 1198 | 2401 | -1.03 [-1.89, -0.11] | PASS |  |
| C_s9_prefix_iid | relay6Cage_st_s9 | cap4 | iid | prefix | seed2701..seed2764 | 128 | 1218 | 2600 | +0.63 [-0.18, +1.47] | PASS |  |
| C_s9_prefix_iid | relay6Cage_st_s9 | prefix | iid | prefix | seed2701..seed2764 | 128 | 1191 | 4916 | -1.61 [-2.43, -0.81] | PASS |  |
| C_s9_prefix_low | relay6Cage_st_s9 | prefix | low | prefix | seed2701..seed2764 | 128 | 1210 | 2411 | -0.04 [-0.84, +0.72] | PASS |  |
| Z_s0 | distill_none_s0 | none | iid | None | seed2701..seed2764 | 128 | 1190 | 0 | — | PASS |  |
| Z_s1 | distill_none_s1 | none | iid | None | seed2701..seed2764 | 128 | 1155 | 0 | — | PASS |  |
| Z_s2 | distill_none_s2 | none | iid | None | seed2701..seed2764 | 128 | 1187 | 0 | — | PASS |  |
| Z_s3 | distill_none_s3 | none | iid | None | seed2701..seed2764 | 128 | 1193 | 0 | — | PASS |  |
| Z_s4 | distill_none_s4 | none | iid | None | seed2701..seed2764 | 128 | 1191 | 0 | — | PASS |  |
| Z_s5 | distill_none_s5 | none | iid | None | seed2701..seed2764 | 128 | 1187 | 0 | — | PASS |  |
| Z_s6 | distill_none_s6 | none | iid | None | seed2701..seed2764 | 128 | 1215 | 0 | — | PASS |  |
| Z_s7 | distill_none_s7 | none | iid | None | seed2701..seed2764 | 128 | 1125 | 0 | — | PASS |  |
| Z_s8 | distill_none_s8 | none | iid | None | seed2701..seed2764 | 128 | 1244 | 0 | — | PASS |  |
| Z_s9 | distill_none_s9 | none | iid | None | seed2701..seed2764 | 128 | 1211 | 0 | — | PASS |  |
| Zrep_s0 | distill_none_rep_s0 | none | iid | None | seed2701..seed2764 | 128 | 1192 | 0 | +0.21 [-0.45, +0.89] | PASS |  |
| Zrep_s1 | distill_none_rep_s1 | none | iid | None | seed2701..seed2764 | 128 | 1142 | 0 | -1.12 [-1.97, -0.37] | PASS |  |
| Zrep_s2 | distill_none_rep_s2 | none | iid | None | seed2701..seed2764 | 128 | 1181 | 0 | -0.46 [-1.32, +0.38] | PASS |  |
| Zrep_s3 | distill_none_rep_s3 | none | iid | None | seed2701..seed2764 | 128 | 1188 | 0 | -0.43 [-1.15, +0.31] | PASS |  |
| Zrep_s4 | distill_none_rep_s4 | none | iid | None | seed2701..seed2764 | 128 | 1190 | 0 | -0.10 [-0.82, +0.70] | PASS |  |
| Zrep_s5 | distill_none_rep_s5 | none | iid | None | seed2701..seed2764 | 128 | 1179 | 0 | -0.63 [-1.47, +0.17] | PASS |  |
| Zrep_s6 | distill_none_rep_s6 | none | iid | None | seed2701..seed2764 | 128 | 1216 | 0 | +0.06 [-0.71, +0.89] | PASS |  |
| Zrep_s7 | distill_none_rep_s7 | none | iid | None | seed2701..seed2764 | 128 | 1130 | 0 | +0.42 [-0.37, +1.16] | PASS |  |
| Zrep_s8 | distill_none_rep_s8 | none | iid | None | seed2701..seed2764 | 128 | 1248 | 0 | +0.34 [-0.40, +1.08] | PASS |  |
| Zrep_s9 | distill_none_rep_s9 | none | iid | None | seed2701..seed2764 | 128 | 1209 | 0 | -0.11 [-0.92, +0.66] | PASS |  |

## e3_theory_cl_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| VA_s0_mix0.05_iid | relay_st_s0 | cap4 | iid | mix0.05 | seed901..seed964 | 128 | 1218 | 2600 | -0.02 [-0.92, +0.86] | PASS |  |
| VA_s0_mix0.05_iid | relay_st_s0 | prefix | iid | mix0.05 | seed901..seed964 | 128 | 1179 | 4902 | -3.19 [-4.12, -2.25] | PASS |  |
| VA_s0_mix0.05_low | relay_st_s0 | prefix | low | mix0.05 | seed901..seed964 | 128 | 1217 | 2404 | -0.08 [-1.03, +0.92] | PASS |  |
| VA_s0_mix0.1_iid | relay_st_s0 | cap4 | iid | mix0.1 | seed901..seed964 | 128 | 1200 | 2600 | -1.47 [-2.39, -0.56] | PASS |  |
| VA_s0_mix0.1_iid | relay_st_s0 | prefix | iid | mix0.1 | seed901..seed964 | 128 | 1181 | 4906 | -3.06 [-4.06, -2.08] | PASS |  |
| VA_s0_mix0.1_low | relay_st_s0 | prefix | low | mix0.1 | seed901..seed964 | 128 | 1207 | 2403 | -0.91 [-1.84, +0.10] | PASS |  |
| VA_s0_mix0.25_iid | relay_st_s0 | cap4 | iid | mix0.25 | seed901..seed964 | 128 | 1194 | 2600 | -1.94 [-2.97, -0.90] | PASS |  |
| VA_s0_mix0.25_iid | relay_st_s0 | prefix | iid | mix0.25 | seed901..seed964 | 128 | 1180 | 4908 | -3.12 [-4.20, -2.08] | PASS |  |
| VA_s0_mix0.25_low | relay_st_s0 | prefix | low | mix0.25 | seed901..seed964 | 128 | 1197 | 2403 | -1.76 [-2.72, -0.72] | PASS |  |
| VA_s0_mix0.5_iid | relay_st_s0 | cap4 | iid | mix0.5 | seed901..seed964 | 128 | 1189 | 2600 | -2.42 [-3.28, -1.54] | PASS |  |
| VA_s0_mix0.5_iid | relay_st_s0 | prefix | iid | mix0.5 | seed901..seed964 | 128 | 1186 | 4903 | -2.67 [-3.57, -1.75] | PASS |  |
| VA_s0_mix0.5_low | relay_st_s0 | prefix | low | mix0.5 | seed901..seed964 | 128 | 1199 | 2396 | -1.58 [-2.55, -0.51] | PASS |  |
| VA_s1_mix0.05_iid | relay_st_s1 | cap4 | iid | mix0.05 | seed901..seed964 | 128 | 1162 | 2600 | -1.91 [-2.83, -1.02] | PASS |  |
| VA_s1_mix0.05_iid | relay_st_s1 | prefix | iid | mix0.05 | seed901..seed964 | 128 | 1143 | 4903 | -3.53 [-4.52, -2.64] | PASS |  |
| VA_s1_mix0.05_low | relay_st_s1 | prefix | low | mix0.05 | seed901..seed964 | 128 | 1164 | 2406 | -1.72 [-2.78, -0.65] | PASS |  |
| VA_s1_mix0.1_iid | relay_st_s1 | cap4 | iid | mix0.1 | seed901..seed964 | 128 | 1161 | 2600 | -2.04 [-3.03, -1.13] | PASS |  |
| VA_s1_mix0.1_iid | relay_st_s1 | prefix | iid | mix0.1 | seed901..seed964 | 128 | 1148 | 4905 | -3.13 [-4.00, -2.36] | PASS |  |
| VA_s1_mix0.1_low | relay_st_s1 | prefix | low | mix0.1 | seed901..seed964 | 128 | 1162 | 2406 | -1.92 [-2.85, -0.95] | PASS |  |
| VA_s1_mix0.25_iid | relay_st_s1 | cap4 | iid | mix0.25 | seed901..seed964 | 128 | 1159 | 2600 | -2.21 [-3.10, -1.34] | PASS |  |
| VA_s1_mix0.25_iid | relay_st_s1 | prefix | iid | mix0.25 | seed901..seed964 | 128 | 1149 | 4904 | -2.99 [-3.81, -2.14] | PASS |  |
| VA_s1_mix0.25_low | relay_st_s1 | prefix | low | mix0.25 | seed901..seed964 | 128 | 1164 | 2398 | -1.76 [-2.80, -0.81] | PASS |  |
| VA_s1_mix0.5_iid | relay_st_s1 | cap4 | iid | mix0.5 | seed901..seed964 | 128 | 1149 | 2600 | -3.04 [-3.87, -2.27] | PASS |  |
| VA_s1_mix0.5_iid | relay_st_s1 | prefix | iid | mix0.5 | seed901..seed964 | 128 | 1147 | 4898 | -3.18 [-3.98, -2.42] | PASS |  |
| VA_s1_mix0.5_low | relay_st_s1 | prefix | low | mix0.5 | seed901..seed964 | 128 | 1162 | 2398 | -1.95 [-2.82, -1.10] | PASS |  |
| VS_s0_FO_K1 | set_full_s0 | prefix | const1 | prefix | seed901..seed964 | 128 | 1248 | 1300 | +2.43 [+1.41, +3.47] | PASS |  |
| VS_s0_FO_K2 | set_full_s0 | prefix | const2 | prefix | seed901..seed964 | 128 | 1217 | 1950 | -0.08 [-1.03, +0.91] | PASS |  |
| VS_s0_FO_K3 | set_full_s0 | prefix | const3 | prefix | seed901..seed964 | 128 | 1205 | 2600 | -1.09 [-1.97, -0.24] | PASS |  |
| VS_s0_FO_K4 | set_full_s0 | prefix | const4 | prefix | seed901..seed964 | 128 | 1204 | 3250 | -1.20 [-2.10, -0.28] | PASS |  |
| VS_s0_FO_K5 | set_full_s0 | prefix | const5 | prefix | seed901..seed964 | 128 | 1193 | 3900 | -2.09 [-2.91, -1.25] | PASS |  |
| VS_s0_FO_K6 | set_full_s0 | prefix | const6 | prefix | seed901..seed964 | 128 | 1187 | 4550 | -2.52 [-3.40, -1.66] | PASS |  |
| VS_s0_FO_K7 | set_full_s0 | prefix | const7 | prefix | seed901..seed964 | 128 | 1178 | 5200 | -3.28 [-4.08, -2.43] | PASS |  |
| VS_s0_relay_agefirst_K1 | relay_st_s0 | prefix | const1 | agefirst | seed901..seed964 | 128 | 1228 | 1300 | +0.83 [-0.21, +1.84] | PASS |  |
| VS_s0_relay_agefirst_K2 | relay_st_s0 | prefix | const2 | agefirst | seed901..seed964 | 128 | 1186 | 1950 | -2.60 [-3.33, -1.85] | PASS |  |
| VS_s0_relay_agefirst_K3 | relay_st_s0 | prefix | const3 | agefirst | seed901..seed964 | 128 | 1185 | 2600 | -2.74 [-3.47, -2.04] | PASS |  |
| VS_s0_relay_agefirst_K4 | relay_st_s0 | prefix | const4 | agefirst | seed901..seed964 | 128 | 1179 | 3250 | -3.19 [-4.06, -2.24] | PASS |  |
| VS_s0_relay_agefirst_K5 | relay_st_s0 | prefix | const5 | agefirst | seed901..seed964 | 128 | 1170 | 3900 | -3.93 [-4.86, -2.90] | PASS |  |
| VS_s0_relay_agefirst_K6 | relay_st_s0 | prefix | const6 | agefirst | seed901..seed964 | 128 | 1188 | 4550 | -2.51 [-3.42, -1.58] | PASS |  |
| VS_s0_relay_agefirst_K7 | relay_st_s0 | prefix | const7 | agefirst | seed901..seed964 | 128 | 1181 | 5200 | -3.08 [-3.91, -2.29] | PASS |  |
| VS_s0_relay_prefix_K1 | relay_st_s0 | prefix | const1 | prefix | seed901..seed964 | 128 | 1270 | 1300 | +4.24 [+3.12, +5.29] | PASS |  |
| VS_s0_relay_prefix_K2 | relay_st_s0 | prefix | const2 | prefix | seed901..seed964 | 128 | 1240 | 1950 | +1.82 [+0.75, +2.85] | PASS |  |
| VS_s0_relay_prefix_K3 | relay_st_s0 | prefix | const3 | prefix | seed901..seed964 | 128 | 1215 | 2600 | -0.23 [-1.05, +0.60] | PASS |  |
| VS_s0_relay_prefix_K4 | relay_st_s0 | prefix | const4 | prefix | seed901..seed964 | 128 | 1197 | 3250 | -1.72 [-2.64, -0.84] | PASS |  |
| VS_s0_relay_prefix_K5 | relay_st_s0 | prefix | const5 | prefix | seed901..seed964 | 128 | 1186 | 3900 | -2.63 [-3.44, -1.78] | PASS |  |
| VS_s0_relay_prefix_K6 | relay_st_s0 | prefix | const6 | prefix | seed901..seed964 | 128 | 1175 | 4550 | -3.55 [-4.48, -2.66] | PASS |  |
| VS_s0_relay_prefix_K7 | relay_st_s0 | prefix | const7 | prefix | seed901..seed964 | 128 | 1176 | 5200 | -3.48 [-4.37, -2.58] | PASS |  |
| VS_s0_setprefix_K1 | set_prefix_s0 | prefix | const1 | prefix | seed901..seed964 | 128 | 1316 | 1300 | +8.05 [+6.87, +9.27] | PASS |  |
| VS_s0_setprefix_K2 | set_prefix_s0 | prefix | const2 | prefix | seed901..seed964 | 128 | 1275 | 1950 | +4.63 [+3.58, +5.65] | PASS |  |
| VS_s0_setprefix_K3 | set_prefix_s0 | prefix | const3 | prefix | seed901..seed964 | 128 | 1307 | 2600 | +7.27 [+6.27, +8.33] | PASS |  |
| VS_s0_setprefix_K4 | set_prefix_s0 | prefix | const4 | prefix | seed901..seed964 | 128 | 1304 | 3250 | +7.03 [+5.98, +8.09] | PASS |  |
| VS_s0_setprefix_K5 | set_prefix_s0 | prefix | const5 | prefix | seed901..seed964 | 128 | 1278 | 3900 | +4.95 [+3.82, +6.13] | PASS |  |
| VS_s0_setprefix_K6 | set_prefix_s0 | prefix | const6 | prefix | seed901..seed964 | 128 | 1253 | 4550 | +2.90 [+1.93, +3.85] | PASS |  |
| VS_s0_setprefix_K7 | set_prefix_s0 | prefix | const7 | prefix | seed901..seed964 | 128 | 1237 | 5200 | +1.56 [+0.62, +2.50] | PASS |  |
| VS_s1_FO_K1 | set_full_s1 | prefix | const1 | prefix | seed901..seed964 | 128 | 1312 | 1300 | +10.74 [+9.61, +11.92] | PASS |  |
| VS_s1_FO_K2 | set_full_s1 | prefix | const2 | prefix | seed901..seed964 | 128 | 1221 | 1950 | +3.09 [+1.92, +4.24] | PASS |  |
| VS_s1_FO_K3 | set_full_s1 | prefix | const3 | prefix | seed901..seed964 | 128 | 1165 | 2600 | -1.67 [-2.58, -0.77] | PASS |  |
| VS_s1_FO_K4 | set_full_s1 | prefix | const4 | prefix | seed901..seed964 | 128 | 1167 | 3250 | -1.52 [-2.42, -0.70] | PASS |  |
| VS_s1_FO_K5 | set_full_s1 | prefix | const5 | prefix | seed901..seed964 | 128 | 1162 | 3900 | -1.96 [-2.80, -1.11] | PASS |  |
| VS_s1_FO_K6 | set_full_s1 | prefix | const6 | prefix | seed901..seed964 | 128 | 1145 | 4550 | -3.40 [-4.22, -2.58] | PASS |  |
| VS_s1_FO_K7 | set_full_s1 | prefix | const7 | prefix | seed901..seed964 | 128 | 1137 | 5200 | -4.02 [-4.80, -3.23] | PASS |  |
| VS_s1_relay_agefirst_K1 | relay_st_s1 | prefix | const1 | agefirst | seed901..seed964 | 128 | 1175 | 1300 | -0.86 [-1.69, -0.08] | PASS |  |
| VS_s1_relay_agefirst_K2 | relay_st_s1 | prefix | const2 | agefirst | seed901..seed964 | 128 | 1158 | 1950 | -2.24 [-3.04, -1.44] | PASS |  |
| VS_s1_relay_agefirst_K3 | relay_st_s1 | prefix | const3 | agefirst | seed901..seed964 | 128 | 1138 | 2600 | -3.93 [-4.70, -3.18] | PASS |  |
| VS_s1_relay_agefirst_K4 | relay_st_s1 | prefix | const4 | agefirst | seed901..seed964 | 128 | 1142 | 3250 | -3.61 [-4.53, -2.78] | PASS |  |
| VS_s1_relay_agefirst_K5 | relay_st_s1 | prefix | const5 | agefirst | seed901..seed964 | 128 | 1147 | 3900 | -3.17 [-3.96, -2.44] | PASS |  |
| VS_s1_relay_agefirst_K6 | relay_st_s1 | prefix | const6 | agefirst | seed901..seed964 | 128 | 1145 | 4550 | -3.33 [-4.17, -2.50] | PASS |  |
| VS_s1_relay_agefirst_K7 | relay_st_s1 | prefix | const7 | agefirst | seed901..seed964 | 128 | 1143 | 5200 | -3.54 [-4.28, -2.83] | PASS |  |
| VS_s1_relay_prefix_K1 | relay_st_s1 | prefix | const1 | prefix | seed901..seed964 | 128 | 1189 | 1300 | +0.35 [-0.47, +1.17] | PASS |  |
| VS_s1_relay_prefix_K2 | relay_st_s1 | prefix | const2 | prefix | seed901..seed964 | 128 | 1182 | 1950 | -0.25 [-1.22, +0.67] | PASS |  |
| VS_s1_relay_prefix_K3 | relay_st_s1 | prefix | const3 | prefix | seed901..seed964 | 128 | 1164 | 2600 | -1.79 [-2.68, -0.87] | PASS |  |
| VS_s1_relay_prefix_K4 | relay_st_s1 | prefix | const4 | prefix | seed901..seed964 | 128 | 1156 | 3250 | -2.43 [-3.25, -1.63] | PASS |  |
| VS_s1_relay_prefix_K5 | relay_st_s1 | prefix | const5 | prefix | seed901..seed964 | 128 | 1146 | 3900 | -3.27 [-4.09, -2.49] | PASS |  |
| VS_s1_relay_prefix_K6 | relay_st_s1 | prefix | const6 | prefix | seed901..seed964 | 128 | 1145 | 4550 | -3.38 [-4.14, -2.61] | PASS |  |
| VS_s1_relay_prefix_K7 | relay_st_s1 | prefix | const7 | prefix | seed901..seed964 | 128 | 1145 | 5200 | -3.32 [-4.16, -2.51] | PASS |  |
| VS_s1_setprefix_K1 | set_prefix_s1 | prefix | const1 | prefix | seed901..seed964 | 128 | 1270 | 1300 | +7.21 [+6.11, +8.21] | PASS |  |
| VS_s1_setprefix_K2 | set_prefix_s1 | prefix | const2 | prefix | seed901..seed964 | 128 | 1260 | 1950 | +6.33 [+5.31, +7.34] | PASS |  |
| VS_s1_setprefix_K3 | set_prefix_s1 | prefix | const3 | prefix | seed901..seed964 | 128 | 1263 | 2600 | +6.59 [+5.57, +7.61] | PASS |  |
| VS_s1_setprefix_K4 | set_prefix_s1 | prefix | const4 | prefix | seed901..seed964 | 128 | 1249 | 3250 | +5.43 [+4.29, +6.64] | PASS |  |
| VS_s1_setprefix_K5 | set_prefix_s1 | prefix | const5 | prefix | seed901..seed964 | 128 | 1249 | 3900 | +5.46 [+4.49, +6.42] | PASS |  |
| VS_s1_setprefix_K6 | set_prefix_s1 | prefix | const6 | prefix | seed901..seed964 | 128 | 1253 | 4550 | +5.77 [+4.73, +6.77] | PASS |  |
| VS_s1_setprefix_K7 | set_prefix_s1 | prefix | const7 | prefix | seed901..seed964 | 128 | 1247 | 5200 | +5.22 [+4.29, +6.17] | PASS |  |

## e3_theory_probe_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| s0_agefirst_cap4 | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1191 | 0 | -2.26 [-3.17, -1.40] | PASS |  |
| s0_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1181 | 0 | -3.05 [-3.84, -2.19] | PASS |  |
| s0_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1184 | 0 | -2.80 [-3.70, -1.90] | PASS |  |
| s0_prefix_cap4 | ? | ? | iid | prefix | seed901..seed964 | 128 | 1230 | 0 | +0.94 [+0.01, +1.89] | PASS |  |
| s0_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1178 | 0 | -3.26 [-4.18, -2.40] | PASS |  |
| s0_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1222 | 0 | +0.35 [-0.54, +1.22] | PASS |  |
| s1_agefirst_cap4 | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1136 | 0 | -4.14 [-4.96, -3.37] | PASS |  |
| s1_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1147 | 0 | -3.17 [-3.99, -2.39] | PASS |  |
| s1_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1150 | 0 | -2.95 [-3.90, -2.04] | PASS |  |
| s1_prefix_cap4 | ? | ? | iid | prefix | seed901..seed964 | 128 | 1166 | 0 | -1.61 [-2.58, -0.70] | PASS |  |
| s1_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1138 | 0 | -3.95 [-4.85, -3.08] | PASS |  |
| s1_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1168 | 0 | -1.39 [-2.35, -0.39] | PASS |  |

## e3_theory_probe_rep_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| s0_agefirst_cap4 | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1191 | 0 | -2.26 [-3.17, -1.40] | PASS |  |
| s0_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1181 | 0 | -3.05 [-3.84, -2.19] | PASS |  |
| s0_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1184 | 0 | -2.80 [-3.70, -1.90] | PASS |  |
| s0_prefix_cap4 | ? | ? | iid | prefix | seed901..seed964 | 128 | 1230 | 0 | +0.94 [+0.01, +1.89] | PASS |  |
| s0_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1178 | 0 | -3.26 [-4.18, -2.40] | PASS |  |
| s0_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1222 | 0 | +0.35 [-0.54, +1.22] | PASS |  |
| s1_agefirst_cap4 | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1136 | 0 | -4.14 [-4.96, -3.37] | PASS |  |
| s1_agefirst_iid | ? | ? | iid | agefirst | seed901..seed964 | 128 | 1147 | 0 | -3.17 [-3.99, -2.39] | PASS |  |
| s1_agefirst_low | ? | ? | low | agefirst | seed901..seed964 | 128 | 1150 | 0 | -2.95 [-3.90, -2.04] | PASS |  |
| s1_prefix_cap4 | ? | ? | iid | prefix | seed901..seed964 | 128 | 1166 | 0 | -1.61 [-2.58, -0.70] | PASS |  |
| s1_prefix_iid | ? | ? | iid | prefix | seed901..seed964 | 128 | 1138 | 0 | -3.95 [-4.85, -3.08] | PASS |  |
| s1_prefix_low | ? | ? | low | prefix | seed901..seed964 | 128 | 1168 | 0 | -1.39 [-2.35, -0.39] | PASS |  |

## e3_trainedq4_panel_20260930

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bb_set_full_s0 | set_full_s0 | prefix | iid | None | seed2401..seed2464 | 128 | 1151 | 5850 | -3.76 [-4.60, -2.94] | PASS |  |
| bb_set_full_s1 | set_full_s1 | prefix | iid | None | seed2401..seed2464 | 128 | 1110 | 5850 | -4.09 [-4.97, -3.20] | PASS |  |
| q4t_s0 | set_fullq4_s0 | prefix | iid | None | seed2401..seed2464 | 128 | 1132 | 5850 | -5.35 [-6.30, -4.42] | PASS |  |
| q4t_s1 | set_fullq4_s1 | prefix | iid | None | seed2401..seed2464 | 128 | 1108 | 5850 | -4.23 [-5.15, -3.30] | PASS |  |
| ref_distill_none_s0 | distill_none_s0 | none | iid | None | seed2401..seed2464 | 128 | 1196 | 0 | — | PASS |  |
| ref_distill_none_s1 | distill_none_s1 | none | iid | None | seed2401..seed2464 | 128 | 1157 | 0 | — | PASS |  |
| ref_maxq | ? | none | None | None | seed2401..seed2464 | 128 | 1497 | 0 | — | None | seed? |
| ref_set_none_s0 | set_none_s0 | none | iid | None | seed2401..seed2464 | 128 | 1230 | 0 | +2.79 [+1.79, +3.79] | PASS |  |
| ref_set_none_s1 | set_none_s1 | none | iid | None | seed2401..seed2464 | 128 | 1228 | 0 | +6.15 [+5.27, +7.04] | PASS |  |

## e3_truncation_cl_v2_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bc_s0 | ? | cap_2 | iid | None | seed901..seed964 | 128 | 1641 | 1300 | +34.73 [+33.04, +36.41] | PASS |  |
| bc_s0 | ? | cap_3 | iid | None | seed901..seed964 | 128 | 1592 | 1950 | +30.73 [+29.09, +32.28] | PASS |  |
| bc_s0 | ? | cap_4 | iid | None | seed901..seed964 | 128 | 1560 | 2600 | +28.08 [+26.57, +29.59] | PASS |  |
| bc_s0 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1559 | 3247 | +27.97 [+26.49, +29.39] | PASS |  |
| bc_s0 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1547 | 3884 | +27.03 [+25.40, +28.70] | PASS |  |
| bc_s0 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1543 | 4477 | +26.64 [+25.14, +28.11] | PASS |  |
| bc_s0 | ? | exact_local | iid | None | seed901..seed964 | 128 | 1593 | 1989 | +30.76 [+29.18, +32.49] | PASS |  |
| bc_s0 | ? | prefix | iid | None | seed901..seed964 | 128 | 1534 | 4909 | +25.94 [+24.46, +27.40] | PASS |  |
| bc_s0 | ? | proxy | iid | None | seed901..seed964 | 128 | 1586 | 2062 | +30.17 [+28.50, +31.97] | PASS |  |
| bc_s0 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1535 | 4396 | +25.97 [+24.44, +27.53] | PASS |  |
| bc_s0 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1531 | 3874 | +25.65 [+24.25, +27.04] | PASS |  |
| bc_s0 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1539 | 4138 | +26.31 [+24.77, +27.77] | PASS |  |
| mix_s3 | ? | cap_2 | iid | None | seed901..seed964 | 128 | 1507 | 1300 | +24.10 [+22.79, +25.47] | PASS |  |
| mix_s3 | ? | cap_3 | iid | None | seed901..seed964 | 128 | 1480 | 1950 | +21.84 [+20.35, +23.28] | PASS |  |
| mix_s3 | ? | cap_4 | iid | None | seed901..seed964 | 128 | 1482 | 2599 | +21.99 [+20.71, +23.31] | PASS |  |
| mix_s3 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1493 | 3248 | +22.93 [+21.79, +24.16] | PASS |  |
| mix_s3 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1448 | 3882 | +19.24 [+18.10, +20.43] | PASS |  |
| mix_s3 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1375 | 4476 | +13.19 [+12.02, +14.37] | PASS |  |
| mix_s3 | ? | exact_local | iid | None | seed901..seed964 | 128 | 1371 | 3112 | +12.87 [+11.86, +13.90] | PASS |  |
| mix_s3 | ? | prefix | iid | None | seed901..seed964 | 128 | 1375 | 4907 | +13.20 [+11.93, +14.41] | PASS |  |
| mix_s3 | ? | proxy | iid | None | seed901..seed964 | 128 | 1386 | 3287 | +14.07 [+12.92, +15.22] | PASS |  |
| mix_s3 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1373 | 4565 | +13.02 [+11.89, +14.18] | PASS |  |
| mix_s3 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1377 | 4254 | +13.37 [+12.24, +14.59] | PASS |  |
| mix_s3 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1379 | 4822 | +13.51 [+12.38, +14.60] | PASS |  |
| scratch_rs_s0 | ? | cap_2 | iid | None | seed901..seed964 | 128 | 1659 | 1300 | +36.22 [+34.46, +38.18] | PASS |  |
| scratch_rs_s0 | ? | cap_3 | iid | None | seed901..seed964 | 128 | 1560 | 1950 | +28.04 [+26.52, +29.65] | PASS |  |
| scratch_rs_s0 | ? | cap_4 | iid | None | seed901..seed964 | 128 | 1508 | 2600 | +23.80 [+22.39, +25.19] | PASS |  |
| scratch_rs_s0 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1410 | 3248 | +15.75 [+14.53, +16.94] | PASS |  |
| scratch_rs_s0 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1397 | 3883 | +14.65 [+13.41, +15.96] | PASS |  |
| scratch_rs_s0 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1382 | 4474 | +13.44 [+12.26, +14.67] | PASS |  |
| scratch_rs_s0 | ? | exact_local | iid | None | seed901..seed964 | 128 | 1378 | 3323 | +13.13 [+11.81, +14.52] | PASS |  |
| scratch_rs_s0 | ? | prefix | iid | None | seed901..seed964 | 128 | 1365 | 4906 | +12.06 [+10.81, +13.34] | PASS |  |
| scratch_rs_s0 | ? | proxy | iid | None | seed901..seed964 | 128 | 1385 | 3268 | +13.70 [+12.47, +15.02] | PASS |  |
| scratch_rs_s0 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1365 | 4532 | +12.07 [+10.81, +13.37] | PASS |  |
| scratch_rs_s0 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1377 | 4175 | +13.03 [+12.02, +14.14] | PASS |  |
| scratch_rs_s0 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1365 | 4817 | +12.09 [+10.95, +13.14] | PASS |  |

## e3_truncation_cl_v3_20260929

| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bc_s0 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1559 | 3247 | +27.97 [+26.49, +29.39] | PASS |  |
| bc_s0 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1547 | 3884 | +27.03 [+25.40, +28.70] | PASS |  |
| bc_s0 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1543 | 4477 | +26.64 [+25.14, +28.11] | PASS |  |
| bc_s0 | ? | prefix | iid | None | seed901..seed964 | 128 | 1534 | 4909 | +25.94 [+24.46, +27.40] | PASS |  |
| bc_s0 | ? | proxy | iid | None | seed901..seed964 | 128 | 1586 | 2062 | +30.17 [+28.50, +31.97] | PASS |  |
| bc_s0 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1535 | 3358 | +25.99 [+24.63, +27.40] | PASS |  |
| bc_s0 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1540 | 3062 | +26.43 [+24.97, +27.87] | PASS |  |
| bc_s0 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1535 | 4396 | +25.97 [+24.44, +27.53] | PASS |  |
| bc_s0 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1539 | 4116 | +26.38 [+24.92, +27.81] | PASS |  |
| bc_s0 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1531 | 3874 | +25.65 [+24.25, +27.04] | PASS |  |
| bc_s0 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1539 | 3590 | +26.31 [+24.85, +27.75] | PASS |  |
| bc_s0 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1539 | 4138 | +26.31 [+24.77, +27.77] | PASS |  |
| bc_s1 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1628 | 3248 | +37.39 [+36.07, +38.78] | PASS |  |
| bc_s1 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1595 | 3883 | +34.63 [+33.40, +35.89] | PASS |  |
| bc_s1 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1585 | 4477 | +33.80 [+32.36, +35.17] | PASS |  |
| bc_s1 | ? | prefix | iid | None | seed901..seed964 | 128 | 1579 | 4903 | +33.28 [+31.95, +34.67] | PASS |  |
| bc_s1 | ? | proxy | iid | None | seed901..seed964 | 128 | 1665 | 2346 | +40.53 [+38.78, +42.39] | PASS |  |
| bc_s1 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1593 | 3425 | +34.47 [+33.19, +35.68] | PASS |  |
| bc_s1 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1598 | 3124 | +34.91 [+33.67, +36.16] | PASS |  |
| bc_s1 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1579 | 4421 | +33.31 [+32.01, +34.56] | PASS |  |
| bc_s1 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1588 | 4155 | +34.03 [+32.80, +35.31] | PASS |  |
| bc_s1 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1590 | 3954 | +34.21 [+32.97, +35.44] | PASS |  |
| bc_s1 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1593 | 3624 | +34.44 [+33.18, +35.63] | PASS |  |
| bc_s1 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1590 | 4061 | +34.24 [+32.85, +35.64] | PASS |  |
| bc_s2 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1539 | 3248 | +26.56 [+25.07, +28.08] | PASS |  |
| bc_s2 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1528 | 3883 | +25.64 [+24.29, +27.05] | PASS |  |
| bc_s2 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1523 | 4477 | +25.20 [+23.70, +26.62] | PASS |  |
| bc_s2 | ? | prefix | iid | None | seed901..seed964 | 128 | 1520 | 4908 | +24.95 [+23.56, +26.32] | PASS |  |
| bc_s2 | ? | proxy | iid | None | seed901..seed964 | 128 | 1553 | 2269 | +27.71 [+26.07, +29.31] | PASS |  |
| bc_s2 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1521 | 3414 | +25.04 [+23.57, +26.49] | PASS |  |
| bc_s2 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1521 | 3144 | +25.04 [+23.59, +26.48] | PASS |  |
| bc_s2 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1523 | 4405 | +25.23 [+24.10, +26.37] | PASS |  |
| bc_s2 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1524 | 4140 | +25.28 [+24.02, +26.56] | PASS |  |
| bc_s2 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1524 | 3964 | +25.30 [+23.98, +26.62] | PASS |  |
| bc_s2 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1519 | 3657 | +24.90 [+23.44, +26.27] | PASS |  |
| bc_s2 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1528 | 4157 | +25.66 [+24.16, +27.18] | PASS |  |
| bc_s3 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1561 | 3248 | +28.50 [+27.04, +29.92] | PASS |  |
| bc_s3 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1563 | 3881 | +28.72 [+27.09, +30.30] | PASS |  |
| bc_s3 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1530 | 4478 | +25.97 [+24.45, +27.42] | PASS |  |
| bc_s3 | ? | prefix | iid | None | seed901..seed964 | 128 | 1518 | 4906 | +24.97 [+23.62, +26.31] | PASS |  |
| bc_s3 | ? | proxy | iid | None | seed901..seed964 | 128 | 1571 | 2184 | +29.35 [+27.76, +30.93] | PASS |  |
| bc_s3 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1513 | 3500 | +24.57 [+23.24, +25.94] | PASS |  |
| bc_s3 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1519 | 3264 | +25.05 [+23.70, +26.43] | PASS |  |
| bc_s3 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1518 | 4421 | +24.96 [+23.71, +26.17] | PASS |  |
| bc_s3 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1516 | 4158 | +24.81 [+23.45, +26.11] | PASS |  |
| bc_s3 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1512 | 3971 | +24.50 [+23.12, +25.83] | PASS |  |
| bc_s3 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1514 | 3672 | +24.69 [+23.33, +26.05] | PASS |  |
| bc_s3 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1523 | 4100 | +25.42 [+24.17, +26.67] | PASS |  |
| bc_s4 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1591 | 3248 | +31.57 [+30.12, +33.13] | PASS |  |
| bc_s4 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1574 | 3882 | +30.14 [+28.61, +31.68] | PASS |  |
| bc_s4 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1564 | 4478 | +29.31 [+28.02, +30.58] | PASS |  |
| bc_s4 | ? | prefix | iid | None | seed901..seed964 | 128 | 1532 | 4904 | +26.66 [+25.48, +27.86] | PASS |  |
| bc_s4 | ? | proxy | iid | None | seed901..seed964 | 128 | 1701 | 2459 | +40.66 [+38.76, +42.78] | PASS |  |
| bc_s4 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1541 | 3538 | +27.40 [+26.03, +28.82] | PASS |  |
| bc_s4 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1544 | 3280 | +27.64 [+26.15, +29.20] | PASS |  |
| bc_s4 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1532 | 4477 | +26.63 [+25.38, +27.92] | PASS |  |
| bc_s4 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1539 | 4237 | +27.25 [+25.86, +28.75] | PASS |  |
| bc_s4 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1534 | 4002 | +26.82 [+25.42, +28.18] | PASS |  |
| bc_s4 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1543 | 3720 | +27.54 [+26.16, +28.99] | PASS |  |
| bc_s4 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1557 | 4034 | +28.75 [+27.41, +30.17] | PASS |  |
| mix_s3 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1493 | 3248 | +22.93 [+21.79, +24.16] | PASS |  |
| mix_s3 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1448 | 3882 | +19.24 [+18.10, +20.43] | PASS |  |
| mix_s3 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1375 | 4476 | +13.19 [+12.02, +14.37] | PASS |  |
| mix_s3 | ? | prefix | iid | None | seed901..seed964 | 128 | 1375 | 4907 | +13.20 [+11.93, +14.41] | PASS |  |
| mix_s3 | ? | proxy | iid | None | seed901..seed964 | 128 | 1386 | 3287 | +14.07 [+12.92, +15.22] | PASS |  |
| mix_s3 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1374 | 3915 | +13.13 [+11.77, +14.55] | PASS |  |
| mix_s3 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1380 | 3761 | +13.63 [+12.30, +14.95] | PASS |  |
| mix_s3 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1373 | 4565 | +13.02 [+11.89, +14.18] | PASS |  |
| mix_s3 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1385 | 4389 | +14.05 [+12.85, +15.30] | PASS |  |
| mix_s3 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1377 | 4254 | +13.37 [+12.24, +14.59] | PASS |  |
| mix_s3 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1375 | 4054 | +13.21 [+11.91, +14.51] | PASS |  |
| mix_s3 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1379 | 4822 | +13.51 [+12.38, +14.60] | PASS |  |
| scratch_rs_s0 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1410 | 3248 | +15.75 [+14.53, +16.94] | PASS |  |
| scratch_rs_s0 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1397 | 3883 | +14.65 [+13.41, +15.96] | PASS |  |
| scratch_rs_s0 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1382 | 4474 | +13.44 [+12.26, +14.67] | PASS |  |
| scratch_rs_s0 | ? | prefix | iid | None | seed901..seed964 | 128 | 1365 | 4906 | +12.06 [+10.81, +13.34] | PASS |  |
| scratch_rs_s0 | ? | proxy | iid | None | seed901..seed964 | 128 | 1385 | 3268 | +13.70 [+12.47, +15.02] | PASS |  |
| scratch_rs_s0 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1376 | 3820 | +12.99 [+11.86, +14.17] | PASS |  |
| scratch_rs_s0 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1373 | 3641 | +12.71 [+11.51, +13.94] | PASS |  |
| scratch_rs_s0 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1365 | 4532 | +12.07 [+10.81, +13.37] | PASS |  |
| scratch_rs_s0 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1374 | 4334 | +12.79 [+11.56, +14.09] | PASS |  |
| scratch_rs_s0 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1377 | 4175 | +13.03 [+12.02, +14.14] | PASS |  |
| scratch_rs_s0 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1374 | 3944 | +12.78 [+11.62, +13.97] | PASS |  |
| scratch_rs_s0 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1365 | 4817 | +12.09 [+10.95, +13.14] | PASS |  |
| scratch_rs_s1 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1433 | 3247 | +20.93 [+19.71, +22.21] | PASS |  |
| scratch_rs_s1 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1438 | 3881 | +21.34 [+20.05, +22.56] | PASS |  |
| scratch_rs_s1 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1418 | 4474 | +19.68 [+18.60, +20.70] | PASS |  |
| scratch_rs_s1 | ? | prefix | iid | None | seed901..seed964 | 128 | 1394 | 4906 | +17.63 [+16.61, +18.60] | PASS |  |
| scratch_rs_s1 | ? | proxy | iid | None | seed901..seed964 | 128 | 1427 | 3588 | +20.43 [+19.34, +21.47] | PASS |  |
| scratch_rs_s1 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1404 | 4014 | +18.48 [+17.41, +19.58] | PASS |  |
| scratch_rs_s1 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1410 | 3885 | +19.00 [+17.84, +20.10] | PASS |  |
| scratch_rs_s1 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1400 | 4607 | +18.15 [+17.11, +19.11] | PASS |  |
| scratch_rs_s1 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1399 | 4425 | +18.06 [+16.85, +19.19] | PASS |  |
| scratch_rs_s1 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1396 | 4314 | +17.83 [+16.77, +18.92] | PASS |  |
| scratch_rs_s1 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1406 | 4170 | +18.63 [+17.53, +19.72] | PASS |  |
| scratch_rs_s1 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1378 | 4768 | +16.32 [+15.33, +17.32] | PASS |  |
| scratch_rs_s2 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1517 | 3248 | +24.71 [+23.42, +26.07] | PASS |  |
| scratch_rs_s2 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1459 | 3883 | +19.95 [+18.72, +21.23] | PASS |  |
| scratch_rs_s2 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1443 | 4476 | +18.65 [+17.46, +19.73] | PASS |  |
| scratch_rs_s2 | ? | prefix | iid | None | seed901..seed964 | 128 | 1421 | 4902 | +16.83 [+15.82, +17.84] | PASS |  |
| scratch_rs_s2 | ? | proxy | iid | None | seed901..seed964 | 128 | 1442 | 3395 | +18.57 [+17.15, +19.90] | PASS |  |
| scratch_rs_s2 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1437 | 3866 | +18.16 [+17.13, +19.28] | PASS |  |
| scratch_rs_s2 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1437 | 3664 | +18.18 [+16.97, +19.45] | PASS |  |
| scratch_rs_s2 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1429 | 4554 | +17.50 [+16.22, +18.82] | PASS |  |
| scratch_rs_s2 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1436 | 4364 | +18.04 [+16.78, +19.34] | PASS |  |
| scratch_rs_s2 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1436 | 4231 | +18.10 [+16.93, +19.34] | PASS |  |
| scratch_rs_s2 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1436 | 3990 | +18.10 [+16.98, +19.29] | PASS |  |
| scratch_rs_s2 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1437 | 4723 | +18.12 [+16.92, +19.44] | PASS |  |
| scratch_rs_s4 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1484 | 3247 | +22.67 [+21.44, +23.88] | PASS |  |
| scratch_rs_s4 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1420 | 3883 | +17.42 [+16.39, +18.50] | PASS |  |
| scratch_rs_s4 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1398 | 4477 | +15.63 [+14.70, +16.54] | PASS |  |
| scratch_rs_s4 | ? | prefix | iid | None | seed901..seed964 | 128 | 1376 | 4910 | +13.73 [+12.55, +14.99] | PASS |  |
| scratch_rs_s4 | ? | proxy | iid | None | seed901..seed964 | 128 | 1388 | 3100 | +14.77 [+13.61, +15.89] | PASS |  |
| scratch_rs_s4 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1378 | 3738 | +13.96 [+12.76, +15.17] | PASS |  |
| scratch_rs_s4 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1386 | 3510 | +14.62 [+13.43, +15.81] | PASS |  |
| scratch_rs_s4 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1378 | 4528 | +13.96 [+12.79, +15.17] | PASS |  |
| scratch_rs_s4 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1385 | 4293 | +14.52 [+13.38, +15.71] | PASS |  |
| scratch_rs_s4 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1381 | 4136 | +14.20 [+13.00, +15.39] | PASS |  |
| scratch_rs_s4 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1387 | 3878 | +14.68 [+13.52, +15.87] | PASS |  |
| scratch_rs_s4 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1381 | 4769 | +14.16 [+13.09, +15.25] | PASS |  |
| scratch_s3 | ? | cap_5 | iid | None | seed901..seed964 | 128 | 1462 | 3247 | +20.41 [+18.99, +21.73] | PASS |  |
| scratch_s3 | ? | cap_6 | iid | None | seed901..seed964 | 128 | 1419 | 3883 | +16.86 [+15.43, +18.36] | PASS |  |
| scratch_s3 | ? | cap_7 | iid | None | seed901..seed964 | 128 | 1393 | 4476 | +14.68 [+13.46, +15.89] | PASS |  |
| scratch_s3 | ? | prefix | iid | None | seed901..seed964 | 128 | 1377 | 4902 | +13.40 [+12.13, +14.74] | PASS |  |
| scratch_s3 | ? | proxy | iid | None | seed901..seed964 | 128 | 1406 | 3420 | +15.72 [+14.37, +17.10] | PASS |  |
| scratch_s3 | ? | proxyage_100 | iid | None | seed901..seed964 | 128 | 1385 | 3954 | +13.99 [+12.77, +15.20] | PASS |  |
| scratch_s3 | ? | proxyage_150 | iid | None | seed901..seed964 | 128 | 1392 | 3782 | +14.59 [+13.27, +15.87] | PASS |  |
| scratch_s3 | ? | proxyage_40 | iid | None | seed901..seed964 | 128 | 1379 | 4575 | +13.55 [+12.35, +14.74] | PASS |  |
| scratch_s3 | ? | proxyage_50 | iid | None | seed901..seed964 | 128 | 1385 | 4405 | +14.01 [+12.79, +15.25] | PASS |  |
| scratch_s3 | ? | proxyage_60 | iid | None | seed901..seed964 | 128 | 1391 | 4268 | +14.52 [+13.33, +15.79] | PASS |  |
| scratch_s3 | ? | proxyage_80 | iid | None | seed901..seed964 | 128 | 1386 | 4046 | +14.12 [+12.96, +15.33] | PASS |  |
| scratch_s3 | ? | tmc_4 | iid | None | seed901..seed964 | 128 | 1378 | 4790 | +13.48 [+12.32, +14.65] | PASS |  |
