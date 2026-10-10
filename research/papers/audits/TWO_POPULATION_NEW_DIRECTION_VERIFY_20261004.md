# Kiểm chứng ba bài review ngày 04/10 (hướng xe–đèn mới, recomposition corpus)

Viết 04/10/2026, 04:1x EDT (wake 2). Người viết là worker; không dùng subagent (người dùng không nói "fetch").

## 0. Phạm vi

**Đã đọc toàn văn:**
- `/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/TWO_POPULATION_NEW_DIRECTION_RESEARCH_20261004.md` (R1, 204 dòng);
- `/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/CORPUS_RECOMPOSITION_20261004.md` (R3, 288 dòng);
- hai đoạn review dán trong tin nhắn người dùng: R1-tóm-tắt và R2 ("Đúng, hướng tiếp theo phải mọc từ những gì đã có").

**Chưa đọc:** `pieces_20261004/inventory.json` và `CORPUS_EVIDENCE_GRAPH_20261004.json`. Chúng là chỉ mục, không chứa khẳng định mới.

**Đã kiểm:**

| Nguồn | Nội dung kiểm |
|---|---|
| `scripts/CITY_env.py` | quan sát và cost |
| `functional.tex:478–500` và `LeanFunctionalRangeEnergyOracleV1.lean:71–90` | inner QP |
| `paper_c.tex:1188–1198, 1410–1416` | limitation về odd |
| Lean | `LeanPaperCBudgetExchangeOddV2.lean:468`, `LeanPaperBParityCriticalV1`, `LeanMarlRepairCalibrationV1.lean:50–70` |
| E3 | `w2b/report.txt` (E2), `e3_wave_20261003/report.txt` (E3a), `w2/report_e7.txt`, `w2/report_e13.txt`, `e9_report.txt` |
| City ledger | C-5 (Q4), C-8 (Q7b), C-10 (G5) |
| Raw city | raw h0 và raw ngẫu-nhiên-hash của cross-play |
| Văn liệu (web) | DC-Ada (repo tác giả), SIL-C, MA-USFA, Li et al. 2020, Assume-Guarantee RL |

**Đã CHẠY thêm** (vì R1 đòi kiểm trace trước mọi train): V1, so tốc độ lệnh với tốc độ thực. 16 run, ledger C-13.

## 1. Bảng kết luận từng khẳng định

Nhãn: ✅ đúng như nói · ◐ đúng nhưng cần chỉnh · ✗ sai / đã lỗi thời · ? chưa kiểm được.

| # | Khẳng định (nguồn) | Kiểm | Kết luận |
|---|---|---|---|
| 1 | Input của đèn có cả halting h lẫn tổng xe n; reward = −halt/10 (R1 §2.1) | `CITY_env.py:57–63`, reward ở `:76` | ✅ Xe bò không "vô hình" với policy. Thêm bằng chứng của tôi: HC-1 bị bác (xe agent bò ÍT hơn xe người, 0.204 < 0.262, C-12). Câu chuyện "hidden queue" yếu từ cả hai phía. |
| 2 | Penalty idle tính trên tốc độ LỆNH nv, không phải tốc độ thực (R1 §2.2, giả thuyết H0) | Code `:137–140`, cộng phép đo V1 (C-13) | ✅ **và mạnh hơn review nghĩ.** Dưới đèn train, 76–99.7 % số quyết định đứng thật đã né penalty bằng lệnh tăng tốc. L-ACT_0 × ACT ra lệnh nv < 0.1 ở 0.000 số quyết định, dù đứng thật ở 10.5 %. Command-cost thấp hơn cost thực khoảng 10 %. Mọi "approach cost" cũ là command-cost: giữ số, đổi nhãn. |
| 3 | DC-Ada = policy chia sẻ đóng băng, học observation transform bằng random search reward-only với CRN (R1 §5) | Repo tác giả: IEEE Access 2026, DOI 10.1109/ACCESS.2026.3687163; baseline gồm shared, random perturbation, local FT, observation normalization; miền warehouse / SAR / mapping | ✅ Collision trực tiếp với "adapter nhỏ + rollout search". Phải là baseline. |
| 4 | SIL-C: cập nhật skill, giữ downstream policy (R1 §5) | NeurIPS 2025 spotlight, arXiv 2509.20612, có backward skill compatibility | ✅ |
| 5 | Li et al. 2020 đã dùng ngưỡng 2 m/s cho low-speed waiting (R1 §3) | Bài tồn tại: JAT, DOI 10.1155/2020/6505893, "Adaptive Traffic Signal Control Model on Intersections Based on DRL"; trang Wiley trả 403 | ? Bài có thật; chi tiết 2 m/s chưa tự xác nhận. Dù sao "ngưỡng 2 m/s" không phải contribution, và tôi không claim nó. |
| 6 | Bảng fleet: dưới ACT 24.97 / 27.91 / 26.01 / 25.63; dưới 4 đèn RL-H 60.55 / 40.20 / 40.97 / 24.68 (R2 §1) | Raw h0 và raw random-hash | ✅ Đây là **city TL khi có fleet**, không phải TL của riêng fleet. 26.01 lấy từ panel random-hash; panel h0 cho 26.30, đúng là jitter. |
| 7 | "Parity 4/160 fail, lệch tối đa ~0.0069 s/xe, chưa xử lý" (R2, R3 §3.2) | Addendum A1, C-11 | ✗ **Đã xử lý, và review đánh giá thấp vấn đề.** Nguyên nhân là thứ tự duyệt `set` theo PYTHONHASHSEED. Biên jitter của MỘT run là **1.45 s/veh** TL và 0.48 cost. Mọi so sánh từng seed (kể cả các chênh lệch trong hình chữ nhật) đều dưới ngưỡng nhiễu này. Kết luận theo trung bình seed giữ nguyên: verdict B1b giống hệt ở cả hai panel. |
| 8 | E9 chỉ bảo đảm tái dựng trên cùng quỹ đạo vật lý; E13: 8/8 điểm OLD âm, CI chứa 0, chưa phải NI (R1 §11, R2 §2, R3 §3.1) | `report_e13.txt` | ✅ **Còn tệ hơn "chưa chứng minh":** cận dưới Bonferroni của agent 8 là −9.43 % (D) và −12.86 % (C). NI theo từng agent thất bại ở mọi margin hợp lý. Endpoint E13-1 (đếm agent có upper < −0.5) là endpoint *phát hiện hại*, không phải NI. Từ nay không dùng chữ "protected". |
| 9 | E2: OP − A0 dương ở cả 2 seed, mọi budget (R2 §3) | `w2b/report.txt:22–25`: L1 [10.65, 1.31], L2 [10.91, 1.55], L5 [2.33, 5.65], L10 [0.49, 7.11] | ✅ Nhưng ở L1/L2, A0 rất kém (new gain −10.6 / −7.1), nên phần lớn chênh lệch là do A0 hỏng. Chỉ 2 seed, panel DEV. E14 (8 seed mới) là phép xác nhận gần nhất và đang trong hàng đợi. |
| 10 | Adapter cảm biến: 6/16, −1.94 s/xe, 13/16 (R2 §4) | C-12 | ✅ Cả hai panel trùng. |
| 11 | Hình chữ nhật 24.83 / 78.51 / 27.30 / 24.36; cost 21.82 / 22.24 (R3 §3.2) | Raw h0 | ✅ Thêm: chênh hai endpoint theo từng seed là [+0.11, +3.11, −0.09, −1.71, −3.77], trung bình −0.47, vô nghĩa thống kê. Ô (RL-H0, L-ACT0) có 31.2 teleport/run và 0.4 xe chưa xong. **Không có endpoint nào tốt hơn**, nên chưa có "bài toán đường đi". |
| 12 | E7: D +3.15 [2.24, 4.07], C +3.28; EMU − FT/PCT chưa phải tương đương; byte 78 058 vs rollback 10 400 (R3 §3.1) | `report_e7.txt` | ✅ Kênh nâng cấp tốn 7.5× byte so với rollback. Phải nói khi so với rollback. |
| 13 | E3a +5.45 [3.27, 7.84], 9/10 (R3 §3.4) | `e3_wave_20261003/report.txt:9` | ✅ |
| 14 | Q4 +8.7 [6.5, 10.6]; 2f(1−f)·8.7 là suy ra từ mô hình (R3 §3.2) | C-5 | ✅ Ledger tự ghi "(derived)". |
| 15 | Q7b: Spearman(K_contract, r) +0.52; có hại trong support (R1 §4, R3 §3.5) | C-8 | ✅ RL-C30/C40 và FT có OOS 0 nhưng r > 0. **Hệ quả cho B4F:** cổng support không thể sửa phần hại trong support (đã ghi trước khi đọc kết quả B4F). |
| 16 | FUNCTIONAL `:482` sai với g < 0; Lean có `0 ≤ g` (R3 M1) | tex `:484` ghi "g ∈ ℝ"; Lean `inner_qp_lower` có `hg : 0 ≤ g` | ✅ **Đã sửa tex** cho khớp Lean (g ≥ 0, tương đương g₊²). Thuật toán `alg:oracle` chỉ đọc công thức "where one cell pair moves", tức gap dương, nên không có kết quả số nào đổi. |
| 17 | C: `recourse_one_odd_all` đóng họ odd m ≥ 3, η ≥ 0; limitation trong manuscript đã cũ (R3 M2) | Lean `:468`, có trong `verify_all` MODS; `paper_c.tex:1414` vẫn ghi "odd m = 5, 7, 9 … numerically; the general one-exchange statement remains open" | ✅ Cần sửa limitation của Paper C: họ g_m odd đã đóng, các count (1,1,2,2), (2,2,2,2) vẫn là số. **Chưa sửa đêm nay**, cần đọc kỹ quantifier trước khi viết lại. |
| 18 | B: `LeanPaperBParityCriticalV1` đã có (R3 M2) | File có, nằm trong MODS | ◐ Có module; chưa tìm thấy câu limitation cũ cụ thể trong `paper_b.tex`. Chưa kết luận manuscript B lỗi thời. |
| 19 | T2 không chứng minh "thêm quyền ⇒ cần thêm dữ liệu" cho cùng một bài toán (R3 M3) | Docstring Lean `:54–58` tự ghi "compares DIFFERENT problems … extra rights can always be left unused" | ✅ Lean đúng; chỉ diễn giải bên ngoài là quá rộng. |
| 20 | MA-USFA (arXiv 2608.11658): ghép policy theo từng agent có thể tệ hơn mọi policy trong thư viện (R3 §6) | arXiv | ✅ Không claim "tốt riêng, ghép lại hỏng". |
| 21 | Reitblatt et al. SIGCOMM 2012, consistent updates (R3 §6) | Bài kinh điển, đã biết | ✅ Không claim "endpoint đúng, intermediate sai" là mới. |
| 22 | Assume-Guarantee RL; Bayesian Policy Reuse (R2) | AG-RL arXiv 2312.09938; BPR đã biết | ✅ Thêm một collision cho cổng B4F mà review chưa nêu: *Contract-Based Compositional Shielding for Safe MARL* (arXiv 2606.14130), mặt nạ hành động cục bộ có chứng nhận. |
| 23 | MATES là adapter đóng băng (R2) | Tìm lại không ra | ? Ghi "chưa xác minh lại"; không dùng làm căn cứ. |
| 24 | V(N,R): thêm quyền / query tùy chọn không làm optimum tệ hơn; hai lower bound chỉ cho max, không cộng (R3 §4C) | Logic | ✅ Đồng ý hoàn toàn. |

## 2. Chỗ tôi phản biện hoặc chỉnh

**P1 — Hướng đi nên là thiết kế 2×2, không chỉ nhánh "xe nâng cấp, đèn đóng băng".**

R1 chọn nhánh fleet nâng cấp. Bằng chứng đêm nay cho thấy hại lớn và có hệ thống nằm ở chiều NGƯỢC LẠI: đèn nâng cấp, fleet đóng băng.
- Đèn RL-H làm city TL lên 60 so với 25 với L-ACT_0.
- Phần lớn biến thiên đến từ fleet (share 0.83).
- Ở chiều fleet đổi phiên bản trước một đèn đóng băng (RL-J_t × L-ACT_t′), city TL chỉ lệch khỏi ACT trong khoảng ±2 s/veh. Tuy vậy đó là đổi seed, chưa phải nâng cấp thật, nên chiều này **chưa được đo**.

Câu hỏi khoa học của R1 là "sửa cách nhìn có đủ, hay phải sửa phản ứng?". Câu trả lời mạnh nhất là một bảng (ai nâng cấp) × (sửa ở đâu). Chiều đèn-nâng-cấp đã có dữ liệu:
- sửa quan sát phía đèn (crawl sensing): −1.9 s/veh, CI chứa 0 trên cost;
- sửa phản ứng phía xe (cổng support): smoke 1 seed cho 50.9 → 29.6; panel đang chạy.

Nếu mẫu hình này lặp lại, đó chính là đóng góp mà R1 mô tả ("xác định phần sửa được bằng quan sát, phần cần sửa phản ứng"). Chi phí thêm chiều thứ hai gần như bằng 0 vì hạ tầng chung.

**P2 — Bước C của R1 (save/load state) nên đổi thành replay pha vòng hở làm phép chính.**

Ghi chuỗi pha của L0 khi chạy với F0, rồi phát lại y hệt chuỗi đó cho F0 và F1 (đèn vòng hở, cùng demand và seed). Mọi khác biệt về xả hàng (số xe qua vạch mỗi pha xanh, start-up lost time, hàng còn lại lúc chuyển đỏ) khi đó là do PHẢN ỨNG của xe. Phép này chính xác, không phải khôi phục RNG hay trạng thái controller, và chạy lại được. saveState để làm phép phụ.

**P3 — Không đợi adapter thất bại mới thử sửa phản ứng.**

R1 xếp sửa phản ứng sau quan sát. Dữ liệu chiều ngược cho thấy sửa phản ứng có thể mạnh hơn một bậc. Sàng lọc cả hai cùng lúc, cùng ngân sách, thì không tốn thêm thời gian lịch.

**P4 — "Upgrade" của fleet phải định nghĩa bằng đại lượng vật lý, và lỗi H0 tự nó là một nâng cấp tự nhiên.**

Theo C-13, command-cost là thước đo sai. F1 được gọi là nâng cấp chỉ khi agent TL (tripinfo), số lần đứng thật hoặc fuel dưới L0 tốt hơn F0 một ngưỡng chốt trước.

Bản fleet sửa lỗi idle (`CarRL` v2: phạt đứng THẬT) là một "phiên bản mới" rất thực tế. Nó đổi phản ứng vật lý: xe không còn đạp ga khi đứng, nên có thể bò khác hoặc khởi hành khác. Đây là F1 tự nhiên nhất cho nhánh của R1.

**P5 — Hình chữ nhật của R3 chưa đủ làm bài toán "đường đi".**

Hai endpoint không khác nhau (mục 11 ở trên). Nhưng cổng B4F là đúng loại "compatibility mode tạm thời" mà R3 §4B(iii) đề xuất. Nếu B4F đạt, trạng thái trung gian xấu (đèn mới, xe cũ) trở nên an toàn mà không retrain. Lúc đó câu hỏi đường đi có nội dung: "light-first + gate" so với "fleet-first" so với "đồng thời", trên một endpoint thật sự tốt hơn. Endpoint tốt hơn phải được TÌM trên SELECT (ma trận 26×25 đang chạy), không chọn hồi cứu.

**P6 — Cổng support không giải phần hại trong support.**

Tôi đồng ý với R1 §4 và R3 §3.5. B4F dưới RL-C50 (τ ≤ 50 theo cấu trúc) sẽ gần như không bắn, mà r ≈ +6. Phần này cần sửa phản ứng TRONG support, ví dụ green-discharge guard hoặc retrain một phần. Ghi trước khi đọc kết quả B4F.

**P7 — Co-training không mới, và tôi không định vị nó là mới.**

B3 có hai vai trò: (a) tạo các cặp (L0, F0) học-cùng-học thật sự, đúng yêu cầu của R1 ("không thay F0 bằng human"); (b) đo partner-specificity. Đồng ý với cả ba review.

**P8 — Một điểm R3 nói chưa đủ mạnh: E13.**

R3 nói "chưa phải NI". Thực tế NI đã thất bại (cận dưới −9 % đến −13 %). H-PROTECT vì vậy không chỉ là giả thuyết; nó có dấu hiệu (8/8 điểm âm) và cần đo đúng: một endpoint NI có margin chốt trước, trên panel mới.

## 3. Chỗ tôi đồng ý và tiếp nhận

- Không claim novelty cho: co-training, adapter đóng băng (DC-Ada), interface compatibility (SIL-C), ngưỡng 2 m/s, cổng OOD/shield (Simplex, 2606.14130), cập nhật tuần tự (HAPPO), consistent updates (Reitblatt), "ghép policy làm hỏng" (MA-USFA).
- Cơ hội novelty duy nhất đáng theo là định lượng và có đối chứng: *trong cập nhật so le giữa hai quần thể học, phần bất tương thích nào sửa được ở quan sát, phần nào phải sửa ở phản ứng; can thiệp tối thiểu đúng chỗ thắng các baseline cùng quyền, cùng dữ liệu và giữ được lợi ích nâng cấp.* Đây vẫn là ứng viên.
- Bẫy rollback (R2, R3 §SUPPORT): mọi endpoint phải giữ được lợi ích nâng cấp tối thiểu chốt trước. Rollback không bao giờ được tính là thắng.
- TEST tách bạch: seed policy của cả hai quần thể, seed traffic mới, tỷ lệ ρ khác, mạng thứ hai. Tách "partner chưa thấy" khỏi "traffic chưa thấy".

## 4. Sửa chữa đã làm và còn phải làm

| Việc | Trạng thái |
|---|---|
| Jitter hash-order (C-11): mọi script city mới bắt buộc PYTHONHASHSEED=0 | Đã làm |
| `functional.tex:484`: g ≥ 0 (khớp Lean) | Đã sửa đêm nay |
| `paper_c.tex:1414`: cập nhật limitation odd theo `recourse_one_odd_all` | Còn nợ; cần đọc quantifier |
| Đổi nhãn "approach cost" thành "command cost" trong report city cũ; `CarRL` v2 (idle thực) có version | Đã ghi C-13; v2 chưa viết |
| Mọi chỗ trong FRAMING / bản thảo E3 nói OLD "được bảo vệ": đổi thành "không phát hiện hại; NI theo từng agent thất bại (cận dưới −9 … −13 %)" | Còn nợ (FRAMING update) |

Thiết kế thí nghiệm đầy đủ và ETA nằm trong `research/papers/audits/TWO_POPULATION_EXPERIMENT_PROGRAM_20261004.md`.

## 6. Deep reading of the two closest collisions (05:46, wake 4)

**MA-USFA**, arXiv 2608.11658, "Is Per-Agent Policy Composition Safe?". Read: abstract and method; experiments from the HTML.
- Lemma 3 (proved by explicit counterexample): independent per-agent recomposition can be strictly worse than every library policy. The cause is that changing teammates changes each agent's environment and makes its per-agent successor features stale.
- Proposition 1: SYNCHRONIZED composition (replaying joint library entries) is unconditionally safe.
- Propositions 4–6: safety holds under supermodular values, a checkable weight-cone condition, or factored transitions.
- Experiments: SFWorld, and **traffic signal control on a 28×7 Manhattan grid (196 signal agents)**.
- Not modelled: frozen deployed teammates, staged deployment, two DIFFERENT populations.

**Consequence for us.** The MECHANISM "a partner change makes the frozen side's learned values stale" is theirs: Lemma 3 in a single signal population. Our fleet-fragility finding (C-12, C-14) is an instance of it in a two-population physical system. It must be cited as such, never claimed as a discovery.

Their "synchronized composition is safe" is the analogue of our "simultaneous upgrade". Job 095 measures that arm, and it is relevant ONLY if simultaneous swaps are a right the operator actually has.

What may remain ours:
- (i) the rights asymmetry: one population frozen, owned by someone else;
- (ii) where to repair (input vs reaction), measured;
- (iii) the always-SUMO / beneficial-fleet foundation, which MA-USFA's setting does not need because its library policies are all useful.

**Contract-Based Compositional Shielding**, arXiv 2606.14130 (abstract and summary only).
- Safety-LTL obligations per agent, projected to action masks.
- An assume-guarantee certificate over the whole contract tuple.
- A bandit selects from a library of obligations during training.
- 6 environments.
- No performance-regression or staged-update setting.

Our guards are performance fallbacks, not safety masks. The shared pattern is "restrict the frozen agent's own actions to what its partner assumptions support". It must be cited next to Simplex. The guard is a baseline-class mechanism.
