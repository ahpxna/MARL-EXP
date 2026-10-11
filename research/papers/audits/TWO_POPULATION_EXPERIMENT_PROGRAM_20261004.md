# Chương trình thí nghiệm hai quần thể (xe × đèn): toàn bộ thiết kế và ETA

Viết 04/10/2026, 04:1x EDT (wake 2), sau khi kiểm ba review (`TWO_POPULATION_NEW_DIRECTION_VERIFY_20261004.md`).

Mỗi thí nghiệm dưới đây có protocol riêng, đóng băng trước khi chạy: dự đoán, ngưỡng, hash, smoke. Tài liệu này là bản đồ: câu hỏi, thiết kế, phụ thuộc, chi phí, trạng thái.

## 0. Câu hỏi trung tâm

> Khi hai quần thể đã học (đèn L, xe F) được cập nhật **so le** (một bên nâng cấp, bên kia đóng băng), bất tương thích nào sửa được bằng **quan sát** của bên đóng băng, bất tương thích nào phải sửa bằng **phản ứng/hành động**? Can thiệp nhỏ nhất đúng chỗ có giữ được (i) lợi ích nâng cấp và (ii) hiệu năng của bên đóng băng, tốt hơn các baseline cùng quyền / dữ liệu / byte không?

**Thiết kế lõi: 2 × 4.**

Hàng — ai nâng cấp:
- **A-L**: đèn nâng cấp, xe đóng băng.
- **A-F**: xe nâng cấp, đèn đóng băng. Đây là nhánh review R1 chọn.

Cột — chỗ sửa:
- (i) input của bên đóng băng;
- (ii) hành động của bên đóng băng (gate / fallback);
- (iii) ràng buộc phản ứng của bên nâng cấp;
- (iv) retrain (bảng riêng, quyền cao hơn).

| | (i) input bên đóng băng | (ii) gate bên đóng băng | (iii) ràng buộc bên nâng cấp | (iv) retrain |
|---|---|---|---|---|
| **A-L** | xe: τ-clip (B4F clip) | xe: fallback khi τ ngoài support (B4F) | đèn: cap max-green (RL-C50, có sẵn) | RL-J (đèn train lại với xe), L-RLH (xe train lại) |
| **A-F** | đèn: q_θ = H + αM₍0.1,2₎ + βM₍2,5₎; H2; H5; normalization; DC-Ada | đèn: fallback sang luật actuated khi input ngoài support train | xe mới: green-discharge guard (nhả cho SUMO lái khi xanh trong vùng xả hàng) | RL-J với F1 (FT đèn), F1 train với hỗn hợp đèn (partner-mixture) |

**Đóng góp ứng viên** (chưa claim): mẫu hình "quan sát đủ / phải sửa phản ứng" phụ thuộc chiều nâng cấp, được giải thích bằng chẩn đoán vòng hở (U3), và can thiệp tối thiểu đúng ô thắng baseline. Mọi khối đã có prior art (DC-Ada, Simplex / shield, cap, FT-mix) đều là BASELINE, không phải phát minh.

## 1. Quy ước chung (mọi thí nghiệm mới)

**Tất định.** PYTHONHASHSEED=0 (C-11). Báo cáo đơn vị là trung bình theo seed; không đọc từng run (jitter 1.45 s/veh).

**Metric vật lý chính** (C-13): city / agent / human TL (tripinfo), số xe xong / chưa xong, teleport, số lần đứng thật, fuel (thiết bị emissions của SUMO, đã bật). Command-cost chỉ là phụ và phải ghi nhãn.

**Seed:**

| Vai trò | Seed |
|---|---|
| SELECT, chọn / tinh chỉnh | traffic 100–104 (đã dùng) |
| TEST | traffic 200–209, demand mới bằng đúng generator của grid4 |
| policy SELECT | t, k = 0, 1 |
| policy TEST | t, k = 2, 3 cho cả hai quần thể |
| ρ | 0.5 chính; 0.25 / 0.75 ở xác nhận |
| Mạng thứ hai | midtown Manhattan (OSM, có sẵn `research/city_sim/net/midtown*.net.xml`) |

**Thống kê.** Bootstrap hai tầng (seed policy × seed traffic), 2000 draw. NI có margin chốt trước. Superiority bằng CI.

**Bẫy rollback.** Mọi phương án phải giữ lợi ích nâng cấp ≥ ngưỡng chốt trước. Rollback chỉ là tham chiếu, không bao giờ là "thắng".

## 2. Danh mục thí nghiệm

### V — Tính hợp lệ (trước mọi kết luận mới)

| ID | Câu hỏi | Thiết kế | Trạng thái / chi phí |
|---|---|---|---|
| V1 | Penalty idle có bị né bằng lệnh? (H0) | `CITY_cmd_realized.py`, 8 cặp × 2 seed | **XONG**, C-13: có, 76–99.7 % |
| V2 | Tất định / jitter | A1: h0 + 5 hash seed | **XONG**, C-11 |
| V3 | Sửa reward (`CarRL` v2: idle thực, tính ở bước sau) đổi hành vi và độ mong manh thế nào? | Train L-ACT-v2_t (t = 0, 1) đối với ACT. So với v1: số lần đứng thật, agent TL dưới ACT; r và city TL dưới RL-H_0..3; tỷ lệ phanh ngoài support (probe FB-5) | ~40 phút (2 train + 40 eval). Protocol trước khi train |

### L — Đèn nâng cấp, xe đóng băng (chiều A-L)

| ID | Câu hỏi | Thiết kế | Trạng thái |
|---|---|---|---|
| L1 | B1 / B1b | xong | **XONG** C-12: hại do fleet quyết định; HC-1 bác; HC-2 không đạt; HC-3 đạt |
| L2 | B4F cổng support phía xe | 13 đèn × L-ACT_0..3 × {fallback, clip}; FB-1…FB-5 đã đăng ký | **ĐANG CHẠY** 38/104 |
| L3 | Cổng trên các fleet khác và mọi đèn | Gate cho L-RLH_t, L-FT_t, fleet co-train × 26 đèn (dùng ma trận B3-X làm plain) | sau B3-X; ~30 phút |
| L4 | Hại TRONG support (RL-C30/C50) cần sửa gì? | Ô (iii)/(iv) của A-L: RL-C50 kết hợp gate; green-discharge guard của xe; FT-mix fleet (fine-tune L-ACT_t với hỗn hợp {ACT, RL-H}) | protocol sau L2 |
| L5 | Ràng buộc khi cập nhật đèn (B4 cũ) | RL-H train lại với phạt regression của fleet (đóng băng L-ACT_t), so với cap / gate / RL-J | sau L4; ~1 h |

### F — Xe nâng cấp, đèn đóng băng (chiều A-F, nhánh R1)

**F0 — Dựng cặp và F1.** Cặp học-cùng-học:
- P-J: (RL-J_t, L-ACT_t), đèn train với fleet đóng băng;
- P-C: (SIM-halt_k đèn, SIM-halt_k xe), co-train;
- P-H: (RL-H_t, L-RLH_t), staged.

F1 (bản nâng cấp của F0):
- (a) **F1-v2**: F0 fine-tune 60 episode đối với L0 đóng băng, dùng `CarRL` v2 (idle thực). Đây là "vendor sửa reward", đổi phản ứng vật lý.
- (b) **F1-FT**: F0 fine-tune 60 episode đối với L0 bằng reward v1 (nâng cấp thuần dữ liệu).
- (c) **F1-new**: fleet train từ đầu đối với L0, seed khác.

**Tiêu chí "là nâng cấp"** (chốt trước): agent TL dưới L0 thấp hơn F0 ≥ 0.5 s/veh trên SELECT. F1 nào không đạt thì loại, không sửa tiêu chí. Chi phí: 4 cặp × 3 F1 ≈ 12 train (~45 phút trên 5 lane).

**F1 — Đo hại.** Dưới L0 đóng băng: F0 so với F1, 5 seed SELECT. Endpoint: human TL, city TL, reward của chính đèn (halting), throughput, phân phối độ dài pha. Câu hỏi: có tồn tại hại cho bên đóng băng không? Nếu KHÔNG có ô nào hại (human / city TL tăng ≤ 0.5): nhánh A-F rỗng, ghi kết quả âm, dồn lực sang A-L. ~20 phút.

**F2 — Sàng lọc sửa quan sát (ô i).**
- Arm: raw, H2, H5, q_θ (lưới α ∈ {0, .25, .5, .75, 1}, β ≤ α: 15 điểm), normalization (khớp moment h theo phân phối lúc train của L0), DC-Ada (random search accept/reject với CRN trên affine-diag 7 chiều, CÙNG ngân sách rollout với lưới q_θ = 15 × 5 seed).
- Tinh chỉnh trên SELECT với ràng buộc F0 không tệ hơn 0.5. Đánh giá trên TEST.
- ~600 run (~40 phút trên 8 lane) + DC-Ada (code 1 h, chạy 30 phút).

**F3 — Chẩn đoán phản ứng (P2 của verify).** Ghi chuỗi pha của L0 với F0, phát lại vòng hở cho F0 và F1 (và human). Đo: số xe qua vạch mỗi pha xanh, start-up lost time, hàng còn lại khi chuyển đỏ, phân phối tốc độ trong 50 m cuối. Phụ: saveState tại 10 mốc, chạy 20 s mỗi fleet. **Dự đoán đăng ký:** nếu F1-v2 đổi xả hàng ≥ 5 % thì ô (i) không đủ cho F1-v2. Code 1 h, chạy 15 phút.

**F4 — Sửa hành động / phản ứng (ô ii, iii).**
- (ii) Đèn fallback sang luật actuated (gap-out 3 s, min 5, max 50) khi (h, n) ra ngoài hộp support lúc train của L0. Đây là no-op trong môi trường train, kiểm bit-identical như G-0.
- (iii) F1 green-discharge guard: trong 30 m trước vạch khi đèn xanh, nhả cho SUMO lái. Giữ tự do eco khi đỏ.
- Đo tỷ lệ override và lợi ích F1 bị mất. ~1 h.

**F5 — Bảng retrain (ô iv).** RL-J với F1 (đèn fine-tune 60 episode, cho phép cập nhật đèn); F1 partner-mixture (train với hỗn hợp {L0, ACT, RL-H}); FT-mix. Bảng riêng. ~1 h.

### P — Đường nâng cấp và chuyển tiếp (H-PATH, R3)

| ID | Thiết kế | Phụ thuộc |
|---|---|---|
| P0 | Tìm endpoint trên ma trận B3-X (SELECT): cặp (L′, F′) tốt hơn hệ đang chạy (ACT, L-ACT_t) theo VECTOR [city TL, human TL, agent TL, teleport], mỗi thành phần không tệ hơn margin. Không có endpoint ⇒ dừng P, ghi kết quả âm | B3-X xong (~05:45) |
| P1 | Bốn góc old/new × old/new cho ≤ 3 endpoint đã chốt, trên TEST (seed 200–209) | P0 |
| P2 | Chuyển tiếp giữa episode: hot-swap policy ở t = 1800 s, giữ nguyên trạng thái vật lý, pha, timer. Thứ tự: light-first, fleet-first, đồng thời, light-first + gate (B4F), fleet-first + guard. Đo delay tích lũy trong cửa sổ 0–900 s sau swap, vi phạm lớn nhất, trạng thái sau ổn định | code swap ~45 phút, chạy ~30 phút |
| P3 | Rollout theo tỷ lệ f (từng phần fleet nâng cấp) — đo thật, thay cho mô hình 2f(1−f) của Q4 | sau P2 |

### X — Chọn checkpoint theo cross-play (H-CROSS)

Từ B3-X: chọn fleet theo hiệu năng tệ nhất / trung bình trên các đèn DEV (seed 0–1), so với chọn theo hiệu năng một mình dưới đèn train. Kiểm trên đèn TEST (seed 2–3) và trên midtown. Không cần train mới. ~30 phút sau B3-X.

### B3 — Co-training (đang chạy, protocol `PROTOCOL_CITY_COTRAIN_20261004.md`)

C-1…C-5 đã đăng ký. Training 4/27 checkpoint xong, sau đó ma trận 650 cấu hình. Vai trò: cung cấp cặp P-C cho F0 và endpoint cho P0; đo partner-specificity.

### G — Tổng quát hóa (xác nhận, chỉ sau khi chốt phương pháp)

- **G1** — TEST traffic 200–209: sinh demand, cùng generator.
- **G2** — Seed policy TEST (2, 3) cho cả hai quần thể: train lại RL-H / L-ACT / RL-J / F1 cho seed mới.
- **G3c** — ρ ∈ {0.25, 0.75}.
- **G4** — Midtown: kiểm mạng và đèn, sinh demand, train RL-H, L-ACT, RL-J, F1 (2 seed mỗi loại), lặp các ô thắng.

### T — Toán (vừa đủ, gắn đúng phương pháp)

| ID | Nội dung |
|---|---|
| T1 | Phản ví dụ hữu hạn: cùng observer và cùng phân phối input, đổi transition response của partner ⇒ return đổi. Folklore, chỉ để chặn claim "sửa input là đủ" |
| T2 | Định lý identity của gate: nếu mọi quan sát trong support train thì policy có gate = policy gốc trên mọi quỹ đạo (đã đo: G-0) |
| T3 | Một cận tách lỗi quan sát–quyết định với lỗi transition-response, giả thiết công khai. Chỉ làm nếu F3 cho thấy cả hai thành phần |

Mỗi định lý cần `#print axioms` và chứng minh giả thiết thỏa được. Đi qua Lean gate trước khi vào bản thảo.

### E3 — Nhánh giao tiếp (paper riêng)

| Mục | Trạng thái |
|---|---|
| E12 | đang chạy, 2/10 seed |
| E14 | xếp sau E12 |
| E8 report | — |
| FRAMING | cập nhật chữ "protected" → NI thất bại (E13) |
| Lean E12-a | — |
| Ngoài kiểm | kiểm ngoài (external benchmark) |

## 3. ETA (đồng hồ thật; máy 10 core; tôi làm liên tục; không tính thời gian người dùng duyệt)

Tốc độ đo được (máy đang tải ~2×):
- một train 120 episode: 8–15 phút;
- một eval 5 seed × 5400 s: 15–60 s;
- ma trận 650 cấu hình: ~35 phút trên 8 lane.

| Giai đoạn | Việc | Thời gian | Mốc sớm nhất |
|---|---|---|---|
| 0 | Thiết kế (bản này + verify) | xong | 04:30 hôm nay |
| 1 | Đêm nay tới 11:00: B3 train → B3-X; B4F; E12, E14; V3; F0 (12 train) → F1; F2 sàng lọc ngưỡng + lưới q_θ; X; P0; protocol từng cái trước khi chạy | ~6 h máy | 11:00 hôm nay |
| 2 | F3 (replay vòng hở), F4 (guard / fallback đèn), DC-Ada, L3–L4, P1–P2 | code ~5 h + máy ~4 h | tối 05/10 |
| 3 | Chốt phương pháp → G1–G3c (seed traffic / policy / ρ mới) | ~6 h máy | sáng 06/10 |
| 4 | G4 midtown (dựng, train 10–12 policy, eval) | ~8 h | tối 06/10 |
| 5 | Lean T1–T2 (+T3 nếu cần), Lean gate; audit kết quả–thuật toán | ~5 h | 07/10 |
| 6 | Bản thảo + hình + audit | ~1.5 ngày | **08–09/10** |

**Kết luận ETA:**
- Nhanh nhất, nếu không có thất bại phải thiết kế lại: khoảng **4.5–5 ngày** tới bản thảo đã xác nhận cho paper hai quần thể, tức ngày 08–09/10.
- Thực tế (1–2 vòng thiết kế lại, ví dụ F1 rỗng hoặc P0 không có endpoint): **7–10 ngày**.
- Paper giao tiếp E3: **2–3 ngày** (E12, E14 xong đêm nay; FRAMING + hình + kiểm ngoài).

**Rủi ro lớn nhất cho ETA:**
- (a) Nhánh A-F rỗng (F1 không gây hại): câu chuyện chuyển hẳn sang A-L. Mất ~0.5 ngày, nhưng vẫn có bài.
- (b) Không endpoint nào tốt hơn ở P0: bỏ phần "đường đi".
- (c) Midtown cần sửa đèn hoặc demand: +1 ngày.

## 4. Infrastructure and queue (updated 05:04 EDT, wake 3, after the user's 04:4x message)

**Spool.** A single sequential runner, `scripts/RUN_spool_20261004.sh`; jobs live in `research/queue_spool_20261004/pending/`. Every job runs with OMP_NUM_THREADS=1, which reproduces the h0 rows bit for bit and brought the load from 41 down to about 13. Each job uses 4 lanes.

**Code in place** (each item smoked, with self-checks where an identity exists):

| Script | Covers |
|---|---|
| `CITY_eval2.py` | lights ACT / FT / ACTP / MP / learned; input adapters q / norm / affine; light fallback box; fleet guards none / fallback / clip / green / green+oos / discharge:D; phase record and open-loop replay (identity verified after two fixes); mid-run handoff of light and/or fleet; fuel, depart-window TL, discharge and start-up delay |
| `CITY_fleet_upgrade.py` | F1 by fine-tuning or from scratch, against any frozen light; reward v1 / v2 (CarRLv2, realized idle) |
| `CITY_dcada_tune.py` | DC-Ada port: accept/reject + CRN, affine transform, budget recorded |
| `CITY_xplay_guard.py` | L4 |
| `CITY_cmd_realized.py` | V1 |
| `SPOOL_eval2_run.sh` | runs a batch of `CITY_eval2` configurations |
| `CITY_green_guard_report.py`, `CITY_wave2_report.py` | reports; written before their data and dry-run |

**Queue:** 010 L4 (running) → 020 F0 trainings → 030 F1 eval + V3 → 040 F3 discharge → 050 P2 handoff → 060 F2 adapters → 070 DC-Ada → 080 L3 guards → 090 MaxPressure. ETA about 07:15 EDT.

**Not yet coded:**
- G4 midtown: NetInfo, demand seeds, training. Q2/Q3 already ran ACT / FT on midtown, so the net loads.
- The light fallback-box calibration job (F4-ii) and the norm-adapter calibration (F2). These are conditional on U-2 finding harm.
- Lean T1 / T2.
- The SUMO SSM device (TTC / safety) as an extra metric. SUMO has it natively (`--device.ssm.probability`), so CoTV's TTC scripts are not needed.

**Repos read for reuse (04:5x):**

| Repo | License | What it has | Decision |
|---|---|---|---|
| DC-Ada | MIT | accept/reject + CRN | Algorithm ported (070). Not cloned. |
| RESCO | GPL-3 | MaxPressure, Cologne / Luxembourg / SLC nets | MaxPressure written from its definition (not copied: GPL). The nets are a candidate third network; a download needs permission. |
| sumo-rl | MIT | standard light obs (density + queue at 0.1 m/s); rewards diff-waiting / pressure / queue | A "published-recipe" light trained with its obs / reward is a possible extra baseline. |
| CoTV | MIT | Flow + RLlib + SUMO 1.10; PressLight, GLOSA, FlowCAV baselines; TTC scripts | Too heavy to adopt. GLOSA already exists in Q2b; TTC via SUMO SSM. Cloning needs permission. |

## 5. Status at 05:45 EDT (wake 3; after the user's B6 addendum)

**Decision gate: B6.** No compatibility claim is made on a non-beneficial fleet (C-17, C-19). Order:
021 (v2 trace, PASS) → 034 (v3 trace, running) → 035 (v3 train, gated) → 036 (B6-1 screen) → 037 (B6-2 on new policy seeds 213 / 313 and fresh traffic 400–409, gated). The exploratory jobs 041–045 follow. Adapter / DC-Ada / handoff are held.

**Second network (G4) — prepared, not started.** RESCO `cologne8` (8 lights, real TAPAS demand 07:00–08:00, CC BY-NC-SA, not redistributed). `NetInfo` controls 8/8 lights. Two points to handle:
- Some lights have 6–8 phases, and `LightRL` drives only the first two greens. Either extend the controller to all greens, or restrict to two-green lights and report it.
- The scenario begins at 25200 s: pass `extra=('--begin', '25200')` and end = 28800.

Midtown (OSM, 234 lights) is the larger alternative.

**E3 side, closed tonight:**
- E12 (L-330): all SUPPORTED.
- E14 (L-331): NOT SUPPORTED. FT-mix / PCT stay the references.
- Lean E12-a `LeanMarlPacketEmulatorV1`: written, compiling.
- FRAMING §5: wording corrections.
- Paper C: the odd one-exchange limitation updated to `recourse_one_odd_all`, which passed the full9 gate with matching source hash.
- FUNCTIONAL: g ≥ 0.

**G4 infra (05:58):** `scripts/CITY_lightk.py` (NetInfoK, LightRLK: keep / advance over ALL greens, 7-dim observation, RL-H reward); smoke on cologne8 with --begin 25200: 8/8 lights cycle through all their greens (2–4), 0 teleports. Lights for the second network must be trained there (grid4 checkpoints are not transferable). sha e5c63e5752db335e.

* G4 light trainer prepared (08:47): scripts/CITY_g4_train_light.py (LightRLK on cologne8, human traffic, --begin 25200, SUMO seeds vary since RESCO ships one route file); smoke 2 x 300 s OK. sha 345ff3bb61c105cc. Not queued (G4 runs after a method freeze).

## Status 10:29 04/10 (supersedes the earlier status lines for the fleet branch)

| Item | Status |
|---|---|
| B6 beneficial learned fleet | Closed negative (C-21 … C-31): recipe, horizon and baseline checked (user step 4). |
| Fleet-upgrade × frozen learned light | Answered with NON-learned fleets: no harm, ACC super-additive, 3 light families, 2 traffic panels (C-30, C-32 … C-34). |
| 2×2 cell "learned fleet upgrade × frozen light" | No valid learned fleet exists in this observation space; the next step is information (SPaT proposal), which needs the user. |
| Held, not run | 060 adapters, 070 DC-Ada, 095 handoff (`hold/`), per the user's step 4. |
| G4 cologne8 | The light recipe does not transfer (C-35, C-36); it needs a different light recipe, registered separately. |
| Claim table | `TWO_POPULATION_CLAIM_TABLE_20261004.md` |
