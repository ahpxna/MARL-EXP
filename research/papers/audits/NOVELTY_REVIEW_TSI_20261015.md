# Novelty của paper TSI: đọc lại toàn bộ (15/10/2026, 13:52 EDT)

User: "đọc lại toàn bộ paper đi, t chưa thấy nó novelty chỗ nào á!"

**Đã đọc:**
- Toàn bộ `research/papers/_tex/paper_two_population.tex` (2157 dòng; PDF 42 trang).
- `COLLISION_SWEEP_TSI_20261006.md`, `PUBLICATION_READINESS_TSI_20261006.md`, `NOVELTY_POSITION_20261003.md`.
- Ledger C-170, C-227, C-228, C-230.

**Tìm thêm hôm nay (không dùng subagent):**
- 5 lượt web search ở chế độ extended. Các chủ đề:
  - xe eco-driving vắng khỏi bộ đếm halting/queue của đèn RL;
  - đèn RL train trên dòng xe người lái bị suy giảm khi có CAV;
  - cảm biến xe ảo / phản thực tế "như xe người lái" trước controller;
  - EAD với đèn actuated (gap-out, extension);
  - dự báo SPaT performative.
- Đọc trang patent Siemens EP3594920A1.
- Đọc bản HTML của HONEST-CAV (arXiv 2602.18740).

Không chạy lại thí nghiệm nào.

## 0. Kết luận

Paper **có** novelty. Nhưng novelty không nằm ở phương pháp TSI: chính paper viết "Forecaster plus adapter is not by itself a novel combination". Novelty nằm ở **một kiểu hỏng mới, nguyên nhân đã được cô lập, và cách sửa không cần train lại**:

1. **Cơ chế.** Xe eco-driving đi theo SPaT lướt chậm tới vạch dừng thay vì dừng hẳn. Vì vậy chúng biến mất khỏi các input "chỉ đếm xe đã dừng" (< 0.1 m/s) của đèn học. Đèn phục vụ hướng đó trễ hơn và giữ đèn xanh lâu hơn, nên chính dự báo mà xe dựa vào tự làm sai mình.
2. **Nguyên nhân là ngưỡng dừng.** Điều này được chứng minh bằng ablation cùng công thức train (W19): chỉ đổi observation thì hại biến mất.
3. **Ngưỡng đó là mặc định của sumo-rl và RESCO (W20).** Nghĩa là phần lớn đèn RL trong benchmark của cộng đồng đều dính.
4. **TSI-G sửa được đèn đã đóng băng** mà không train lại và không cần search reward.

Vấn đề là novelty này **bị giấu**:
- Nó chỉ xuất hiện ở **trang 34/42**.
- Tiêu đề, abstract, mục The Gap (trang 5) và danh sách đóng góp vẫn viết theo câu chuyện **trước W19** (06/10). Trong câu chuyện đó, cơ chế "chưa được cô lập" và phương pháp "không mới".

## 1. Bảng novelty

| # | Claim | Gần nhất | Paper này thêm gì | Bằng chứng | Collision | Ở đâu trong paper |
|---|---|---|---|---|---|---|
| N1 | **Vòng tự phá:** xe glide rời khỏi input có ngưỡng dừng của đèn học, đèn kéo dài xanh, dự báo SPaT sai thêm | Bottom 2000, Perdomo 2020 (khái niệm chung); Genser T-ITS 2024, Discussion (định tính, đèn actuated, timestamp detector đổi); Erdmann 2013 (GLOSA và đèn adaptive xung đột); Maadi 2022 (co-train, tỉ lệ queue tăng theo share); **HONEST-CAV 2026** (đèn MARL quan sát queue length và ước lượng SPaT bằng cách chạy chính policy trên trạng thái hiện tại; vòng phản hồi có mặt nhưng không được phân tích) | Chỉ ra **kênh cụ thể** (ngưỡng 0.1 m/s) và **đo** nó: sai số khi công bố 3.02 s so với 1.70 s khi tính mà không công bố; halting 2.9 → 1.6; xanh 15.0 → 17.1 s; xe fleet +1.7 đến +2.3 s/veh trong khi xe người lái −1.3 | Mạnh trong mô phỏng (đăng ký trước, 5×4×20) | NOT FOUND cho cơ chế cụ thể (06/10 và 15/10) | VII-E Diagnosis (tr. 19); Thm 3–4 ở mục VI (tr. 16–18) |
| N2 | **Cô lập nguyên nhân:** ablation cùng công thức train, 10 họ đèn (W19) | Chưa thấy ai | Chỉ đổi observation: đèn đếm theo dải tốc độ / vị trí không bị hại (−0.39 / −0.40 so với +1.70 s/veh; DiD −2.09 [−2.78, −1.36]); reward không ngưỡng giảm hại khoảng một nửa (+0.85); hằng số ×½ / ×2 không đổi pattern. **Dự đoán đăng ký trước cho MaxPressure đã đúng** (W9-6: xanh 18.1 → 18.0 s, một mình phía fleet là đủ) | Mạnh (α 0.025; DiD có ý nghĩa) | NOT FOUND | VII-R (tr. 34) |
| N3 | **Mặc định của cộng đồng bị dính** (W20) | Tài liệu và code của RESCO / sumo-rl định nghĩa ngưỡng này; chưa ai thử với fleet eco-driving | sumo-rl default +5.36, RESCO IDQN/IPPO +2.63, MPLight +16.02 s/veh; xanh dài thêm 15–30 %; `wave` (không ngưỡng) không bị hại. **Có density, approach hay speed nằm cạnh cũng không cứu được**, nên policy học thực sự dựa vào feature có ngưỡng. Đây là điểm không hiển nhiên | Mạnh với công thức của ta; dùng DQN của ta, không phải learner hay action space của thư viện; chỉ grid4 | NOT FOUND (09/10, 15/10) | VII-S (tr. 34) |
| N4 | **TSI-G:** cảm nhận mỗi xe fleet như "bản sao người lái" mà nó thay thế; 1 tham số site (CREEP), không train lại, không search reward | Siemens EP3594920A1 (đưa detector ảo **dự báo trước** vào controller không đổi để GLOSA ổn định; **không** mô phỏng xe được tư vấn như xe người lái); DC-Ada, MATES, Huang ICAPS 2026 (adapter học được); RobustLight, MDRC (khôi phục quan sát khi cảm biến hỏng) | Sửa một dịch chuyển **do quần thể đối tác gây ra** bằng một phản thực tế vật lý, không học. Một lớp duy nhất áp cho mọi representation: đạt mọi giới hạn trên RL-H, sumo-rl, RESCO IDQN; MPLight bỏ được 97 % tác hại nhưng không đạt (+0.51, cận trên +0.74) | Vừa–mạnh; chỉ grid4; cần V2X để biết xe nào thuộc fleet | NOT FOUND cho ý cụ thể; họ "input ảo trước controller không đổi" đã có | IV-I (tr. 10), VII-S |
| N5 | **Công bố quantile thấp** (q = 0.1) thay vì trung vị | EP3985636 (map quantile vào minEnd / likely / maxEnd); Mahler & Vahidi 2014; Xue 2026 (phía xe); quy tắc an toàn của EAD (dùng min time-to-change cho đèn xanh) | Thành phần đã có, nhưng thêm ba điều: (a) quantile là biến hiệu chỉnh phía hạ tầng cho fleet đã đóng băng; (b) nó lật dấu kết quả fuel dưới PHEMlight5 (+1.79 % → −2.23 % trên cùng các hàng W13), cơ chế là **tái tăng tốc sau khi glide** (phân rã theo chế độ lái); (c) tiết kiệm hơn train lại fleet 1.5–2.6 điểm. Field: SPaT Tampa phát cận dưới; Hamburg q0.1 giữ calibration | Mạnh trong mô phỏng (3 panel + default trên policy mới) | COMPONENT (incremental) | VII-L đến VII-N (waves 13–15, tr. 29–31) |
| N6 | **Bài toán:** hai quần thể học, khác chủ, đều đóng băng, chỉ được sửa interface | Co-train (CoTV, HONEST-CAV, Busch, Maadi, Jiang 2022, Paine 2025); FoRL (train lại đèn); tương thích ngược trong ML (Bansal, Shen); STAMP (adapter hai phía, không có vòng kín) | Đặt bài toán này trong giao thông | Là framing; ý nghĩa thực tế bị W16–W18 thu hẹp | NOT FOUND (giao thông), PARTIAL (ML) | Intro, IV-C (tr. 6) |

"NOT FOUND" là kết quả tìm kiếm có giới hạn, không phải chứng nhận "novel". Paper không nên dùng chữ "first".

## 2. Không phải novelty (nói thẳng)

- **Bộ dự báo:** MLP quantile với pinball loss (Genser, Eteifa, EP3985636). Paper đã tự nói vậy ở II-C.
- **Provider lai "exact khi vàng":** rất phổ biến; dữ liệu Tampa cho thấy hết đèn vàng vốn đã được báo chính xác.
- **Adapter đếm theo dải tốc độ:** thuộc họ input adapter đã có.
- **Ghép dự báo + adapter:** paper tự nói là không mới.
- **GLOSA giảm hiệu quả khi đèn adaptive:** đã biết (Stevanovic 2013, NYSERDA 2019, Bodenheimer 2014).
- **Dự báo tự phá nói chung:** Bottom 2000, Perdomo 2020.
- **4 định lý:** sơ cấp (xét hết các trường hợp hữu hạn, đại số, union bound). Chúng minh họa được, nhưng tự thân không phải đóng góp. Riêng Thm 4 (hàng đợi) có ích như công cụ **dự đoán**: nó báo trước MaxPressure không cần adapter, và kết quả đúng như vậy.
- **Đăng ký trước, crossed bootstrap, đủ mọi thất bại:** là độ chặt chẽ, hiếm trong lĩnh vực này nên là điểm mạnh, nhưng không phải novelty.
- **Midtown:** minh họa khả năng chuyển giao. Đèn B2D không có input ngưỡng nên **không kiểm tra cơ chế lẫn phía đèn của TSI**.
- **Kiểm tra field:** là kiểm tra độ thực tế. Việc "mô hình lái xe làm đổi lợi ích eco-driving" đã biết chung; con số cụ thể 8.7 % → 1.1 % là một kết quả âm có ích.

## 3. Vì sao đọc không thấy novelty

1. **Vị trí.** W19/W20 nằm ở trang 34/42. Trước đó là khoảng 30 trang gồm M1–M4, các comparator (port DC-Ada, FoRL), waves 9–15 và field.
2. **Tiêu đề** nói về TSI, đúng cái mà chính paper bảo không mới. Cái mới (ngưỡng dừng, mặc định của thư viện, TSI-G) không có trong tiêu đề.
3. **The Gap (dòng 234–243, tr. 5)** được viết ngày 06/10, trước W19/W20, và tự phủ nhận: "we make no state-of-the-art or 'first' claim. Forecaster plus adapter is not by itself a novel combination; the contribution is the closed-loop diagnosis, its formal model, and the confirmed and replicated two-sided calibration procedure". Đoạn này không nhắc W19, W20 hay TSI-G. Người đọc sẽ rút ra: "chỉ có một quy trình".
4. **Paper tự mâu thuẫn về điều mới nhất của nó:**
   - Contribution 3 (dòng 108–109) và tiêu đề H3 (dòng 1866) viết "no single mediator isolated".
   - Thân H3 (dòng 1871) và mục VII-R viết "the mediator is the input's stop threshold".
   - Conclusion (dòng 1982–1983) viết "without identifying every mediator".
5. **Có 10 contribution, phần lớn là quy trình** (benchmark, "negative map", các wave đăng ký trước). Những cái mới thật là mục 8–9, nằm cuối danh sách.
6. **Abstract khoảng 450 từ** (TR-C giới hạn 250), khoảng 25 con số. Cơ chế xuất hiện ở dạng rào đón ("three diagnostics support a closed-loop account"), và abstract kết thúc bằng giới hạn.
7. **Mỗi câu claim mang 2–3 lớp rào đón.** Nói trung thực là đúng, nhưng các giới hạn nên gom về một chỗ (Claim boundary / Limitations) thay vì rải vào từng câu.

## 4. Phản biện mạnh nhất về ý nghĩa, và câu trả lời

- **"Hiển nhiên: đèn đếm xe dừng thì không thấy xe đang chạy."** Câu trả lời:
  - (a) Vòng phản hồi làm dự báo hại chính thời gian của fleet, trong khi xe người lái lại được lợi.
  - (b) Density, approach count hay speed nằm cạnh **không** bảo vệ được (sumo-rl, RESCO drq).
  - (c) Đây là mặc định của benchmark.
  - (d) Sửa được mà không train lại.
  - (e) Dự đoán MaxPressure được đăng ký trước và đã đúng.
- **"Với tài xế khớp dữ liệu thực, fleet chỉ lợi khoảng 1 %, vậy sửa để làm gì?"** Đây là phản biện nặng nhất, và chưa trả lời được.
  - Tác hại của cơ chế nằm ở **thời gian** (+1.7 s/veh với RL-H, +2.6 đến +16 s/veh với các state của thư viện), nhưng mới chỉ đo trong thế giới Krauss. *(Sửa 15/10 14:43: bản đầu ghi "+2.6 đến +16", bỏ sót RL-H +1.7.)*
  - W16/W17 dừng trước bước TSI vì fleet không có lợi ích về fuel, nên chưa ai biết cơ chế còn gây hại trong thế giới tài xế thực hay không.
- **"Chỉ có mô phỏng, lưới tổng hợp."** Midtown không kiểm tra cơ chế, vì đèn B2D không có input ngưỡng.

**Hai thí nghiệm rẻ nhất làm novelty có trọng lượng** (chỉ đề xuất, chưa đăng ký, chưa chạy):
- (i) Chạy arm SV so với R của W20 (sumo-rl default, RESCO drq) trong thế giới W17 (IDM khớp field). Mục đích: xem tác hại về thời gian còn không khi tài xế giống người thật.
- (ii) Chạy cùng cặp SV / R với đèn họ sumo-rl default trên Midtown. Mục đích: xem cơ chế có xuất hiện trên bản đồ thật không.

## 5. Đề xuất viết lại theo hướng novelty-first (bản nháp, chưa áp vào .tex)

### Tiêu đề (chọn 1)

- *When Gliding Cars Leave the Queue: Learned Traffic Signals That Count Stopped Vehicles Defeat Eco-Driving Fleets, and a Repair Without Retraining*
- *Stop-Thresholded Observations Make Learned Signals Defeat the Eco-Driving Fleets That Rely on Them: Diagnosis and a Retraining-Free Sensing Repair*

### Abstract (sau các sửa ở mục 8)

> Learned traffic signals usually count a vehicle as waiting only once it has almost stopped (below 0.1 m/s), in halting counts, queues, waiting times and pressures. In SUMO on a 16-signal grid, eco-driving vehicles following signal timing (SPaT) glide towards the stop line instead of stopping, drop out of these inputs and are served later: the learned signal lengthens its greens, and the forecast the vehicles rely on defeats itself. A frozen PPO fleet that saves fuel under fixed-time signals loses this benefit after the upgrade. A same-recipe ablation over ten signal families identifies the cause as the stop threshold of the signal's inputs: signals trained identically but observing speed or position bands were not harmed, while with the halting count the harm persisted under a threshold-free reward and other scale constants. The exposed inputs are the defaults of sumo-rl and RESCO; re-implemented and trained by our recipe, they let the forecast cost the fleet's vehicles 2.6–16.0 s/veh. Neither policy needs retraining: a two-sided interface (a quantile forecast for the fleet, a speed-binned count for the signal) passed a registered confirmation (second attempt) and two fresh-policy replications, and with a low published quantile saved fuel under two emission models, 1.5–2.6 points more than fleet retraining (HBEFA4); TSI-G, which senses each fleet vehicle as the human-driven twin it replaces, met every limit on three of four signal families and removed 97% of the harm on the fourth. Against drivers matched to field trajectories the fleet's own benefit falls to about 1%.

### Contributions (4 mục, thay cho 10)

1. **A failure mode and its cause.** We identify a closed loop between SPaT-following eco-driving fleets and learned signals: gliding vehicles leave the signal's stop-thresholded inputs, greens lengthen (11–30%), the published forecast's error at the fleet's queries nearly doubles (1.70 to 3.02 s), and the fleet's vehicles lose time. A same-recipe ablation over ten signal families isolates the input's stop threshold as the main cause and the reward's as a secondary one; a threshold-queue model predicts which signals are exposed, and a registered prediction for max-pressure control held.
2. **The exposure is the benchmark default.** The default representations of sumo-rl and of RESCO's IDQN/IPPO and MPLight contain such inputs; trained by our recipe, they cost the fleet 2.6–16.0 s/veh, although some of them also observe density, approaching vehicles or speeds.
3. **Repairs that retrain neither population.**
   - TSI (a calibrated quantile forecast and a speed-binned count) passed a registered confirmation and fresh-traffic and fresh-policy replications.
   - Publishing a low quantile kept its saving under two emission models and exceeded fleet retraining by 1.5–2.6 points.
   - Task ports of DC-Ada and FoRL did not meet the limits.
   - TSI-G (human-twin sensing, one site parameter, no reward search) met every limit on three of four signal families and removed 97% of the harm on MPLight.
4. **Boundaries, all reported.** These are the conditions under which the failure does not arise or the repair does not hold:
   - recorded Salt Lake City demand;
   - a one-lane network;
   - IDM driving;
   - drivers matched to field trajectories (fleet benefit about 1%);
   - a transfer to the full Midtown Manhattan map.

   Every experiment was registered before it ran and every failure is reported.

### The Gap (thay dòng 234–243)

> Self-defeating forecasts are known in transportation \cite{bottom2000} and studied as performative prediction \cite{perdomo2020}. At actuated signals, vehicles that plan with time-to-green predictions were expected to shift detector timestamps \cite{genser2024}, and the tension between GLOSA and adaptive control was noted early \cite{erdmann2013}. Cooperative designs avoid the problem by training or co-designing both sides \cite{guo2023,zhang2026,maadi2022}, or by retraining the signal to keep its own forecasts \cite{gerner2026forl}; HONEST-CAV's signal observes lane queue lengths (with occupancy and speed) and estimates the upcoming SPaT by running its own policy on current observations, without analysing the feedback through the queue \cite{zhang2026}. Input-side modules repair frozen signal policies against sensor corruption \cite{li2025robustlight,li2026mdrc}, and predicted (virtual) detector inputs give an unchanged controller earlier arrivals \cite{siemens2020ep}. We found no study that (i) identifies the channel through which a learned signal defeats SPaT-following vehicles, namely its stop-thresholded observation, and isolates it by changing only the observation under an identical training recipe; (ii) shows that this channel is built into the default representations of the most used open-source benchmarks; or (iii) repairs it with both learned policies frozen, in particular by sensing fleet vehicles as the human-driven vehicles they replace. Our forecaster and speed-binned count are not new as components; the contribution is the mechanism, its reach, and the retraining-free repairs.

### Sắp xếp lại phần Results (đề xuất)

1. **Vấn đề:** M1–M2.
2. **Cơ chế:** diagnosis, W19, Thm 4, dự đoán MaxPressure (W9-6).
3. **Phạm vi:** W20.
4. **Cách sửa:** TSI (confirmation, replications, quantile, comparators) và TSI-G.
5. **Ranh giới:** các mạng khác, IDM và tài xế khớp field, Salt Lake, Midtown.

Chi tiết port DC-Ada/FoRL, các biến thể W15 và lịch sử các lần thử spider chuyển sang phụ lục. Như vậy thân bài có thể còn khoảng 20–25 trang.

### Sửa nhất quán (bắt buộc dù có viết lại hay không)

- Dòng 108–109 (contribution 3), dòng 1866 (tiêu đề H3), dòng 1982–1983 (Conclusion): sửa "no single mediator isolated" thành "the mediator is the input's stop threshold (W19); which learned feature carries it inside each policy is not isolated".
- Related work II-D: thêm chi tiết HONEST-CAV (quan sát queue length, ước lượng SPaT bằng rollout policy). Lưu ý định nghĩa QLen của họ **chưa kiểm**. Ghi thêm rằng W15-6 (policy-aware forecaster) là cùng ý tưởng, và không thêm được tiết kiệm.
- Nên trích (cần kiểm trước khi đưa vào): Genders & Razavi 2018, so sánh các state representation cho đèn RL. Đây là nền cho W19, không phải collision.

## 6. Nguồn tìm hôm nay

- HONEST-CAV, arXiv 2602.18740 (HTML): "we first estimate the upcoming SPaT by executing the trained policy based on currently observed intersection states". Signal state gồm Occ, AvgSpd, QLen, CAVPR; phần xe (MLTPA) lấy từ công trình trước và ghép lúc đánh giá. Đây là bản tóm tắt của WebFetch, một lượt đọc.
- Siemens EP3594920A1 (Google Patents, 100k ký tự đầu): detector ảo dự báo trước 20–35 s, đưa vào controller adaptive không đổi; không mô hình hóa phản ứng của xe được tư vấn.
- Không ra collision:
  - CAVLight (TR-C 2024, quan sát lệch ở penetration thấp);
  - IoT-TSC arXiv 2606.22108 (dùng ngưỡng 0.1 m/s để đo delay, không phải cơ chế);
  - Hao et al. EAD cho đèn actuated (quy tắc min/max time-to-change);
  - FHWA Signal Timing on a Shoestring (gap-out / extension).

---

# Phần 2 (15/10/2026, 14:50 EDT): gom giới hạn về một chỗ, kiểm lại nháp, giảm độ dài

User: "các giới hạn nên gom về một chỗ … tìm các chỗ như v và nhóm lại trong nháp của m đi, xong đọc lại paper 10 lần, xong r coi lại
các chỗ trong nháp của m đúng chưa? r xem những chỗ nào làm dc để giảm độ dài paper xuống".

## 7. Gom giới hạn về một chỗ

### 7.1 Nguyên tắc

Chỉ giữ một qualifier ngay trong câu claim khi thiếu nó câu đó sai hoặc gây hiểu lầm. Những qualifier phải giữ:
- bối cảnh: SUMO, Krauss, grid4;
- tên mô hình phát thải bên cạnh con số fuel (HBEFA4 / PHEMlight5);
- "re-implemented, trained by our recipe" cho các họ của thư viện;
- "second attempt" cho lần confirmation;
- verdict "not shown" của các phép thử đăng ký trước.

Mọi giới hạn còn lại chỉ nói một lần, trong một mục duy nhất (7.2). Các mục khác chỉ báo số và verdict.

Mức lặp hiện tại (đếm theo câu, regex, lượt 1):

| Chủ đề | Số câu | Số mục chứa nó |
|---|---|---|
| Mô hình phát thải | 48 | 19 |
| IDM | 33 | 15 |
| Krauss / mô phỏng / tài xế thực | 32 | 18 |
| Tổng quát theo mạng | 36 | 13 |
| "mediator / descriptive" | 28 | 19 |
| Equivalence / NI | 18 | 14 |
| Phạm vi của các định lý | 10 câu | 8 chỗ |

Phạm vi các định lý được nói lại ở các dòng 42, 78, 226, 863–868, 892–893, 976–983, 994, 996–999, 1868 và 1972.

### 7.2 Mục "Claim Boundary and Limitations" (bản dán vào paper)

Mục này thay ba chỗ hiện có:
- Claim boundary (dòng 132–142);
- Shortcomings and Limitations (dòng 1902–1955, khoảng 1.190 chữ);
- câu cuối của Conclusion.

Độ dài khoảng 480 chữ.

```latex
\subsection{Claim Boundary and Limitations}\label{sec:limits}
Every qualification of the results is stated here once; the other sections report numbers and registered verdicts.
\begin{itemize}\setlength\itemsep{1pt}
\item \emph{Simulation and human drivers.} All results are from SUMO. The main results use SUMO's Krauss drivers, which brake later and
harder at a stop than measured drivers (F4). Against drivers matched to measured car following and stop approaches, a fleet trained in that
world saved 1.10\% fuel under HBEFA4 and none detectable under PHEMlight5 (W17), and five further fleet designs stayed below 3\% (W18). Under
IDM the quantile revision removed the fleet's time cost but not its fuel loss (W15-3a). With field-matched drivers the closed loop persists
(W21-A: harm beyond the threshold-free control for AH, sumo-rl and MPLight, not shown for RESCO IDQN), but the forecast alone saves no
fuel there and costs the fleet time even under the threshold-free control. No experiment combines a real learned signal with a real fleet.
\item \emph{Fuel model.} Fuel is SUMO's emission model. The original design's saving reverses under PHEMlight5 ($+1.76\%$), the model that
measured fuel favours (F2); the quantile revision saves under both models on every grid4 panel tested. A saving under both models is not a
field measurement.
\item \emph{Networks and demand.} TSI met the limits on grid4, on rand3 (second attempt, widened adapter range) and on a two-lane rebuild of
spider, and failed on the original one-lane spider in six attempts. On recorded Salt Lake City demand the learned signal stayed close to the old plan
(mean green $-16\%$) and the old timing kept the fleet's fuel benefit, but, as on every synthetic network, cost its vehicles time
($+1.3$\,s/veh against no SPaT; C-245). The Midtown transfer uses random demand, keeps the 56 multi-phase junctions on actuated
programs and compares with SUMO's actuated controller, not the city's system. There the forecast alone cost the fleet's vehicles about
9\,s/veh against no SPaT under both a halting-count family and the threshold-free control (W21-B), so the stop-threshold loop was not
separated from a larger harm common to both, whose source is not isolated.
\item \emph{Signals.} The learned signals are keep-or-switch double DQNs. The sumo-rl and RESCO representations were re-implemented and
trained by our recipe, not with the libraries' learners or action spaces. TSI-G needs each vehicle's fleet membership (V2X), has one site
parameter, was tested on grid4, and did not meet the limit on MPLight.
\item \emph{Comparators.} DC-Ada and FoRL were ported to this task (a first DC-Ada port was withdrawn after an audit); neither is a
reproduction of the published benchmark. Retraining is one recipe (F1-B). We make no state-of-the-art or ``first'' claim.
\item \emph{Channel and sensing.} Delay and loss are modelled by a per-link query cache, not a periodic broadcast; sensing errors perturb only
the adapter's count.
\item \emph{Calibration.} Each forecaster needs eight logged episodes of its deployed signal. One adapter setting held on grid4, but rand3
needed a wider grid. Transfer of a simulation-calibrated provider to the field is untested.
\item \emph{Mechanism and formal results.} The diagnostics and W19 place the cause in the input's stop threshold; which learned feature
carries it inside each policy is not isolated. The theorems concern stylized models (finite cases, a threshold queue, a union bound) under
their stated hypotheses, not the simulator or the learned controllers.
\item \emph{Inference.} Verdicts are registered one-sided tests, with Bonferroni chains over repeated attempts whose bounds assume each
bootstrap test holds its nominal level. ``Not shown'' is not evidence of harm, and ``no difference detected'' is not equivalence. Post-hoc
analyses are labelled. The first confirmation chain reused one set of checkpoints and lacks launch-time input hashes; later panels use newly
trained policies and record provenance at capture.
\end{itemize}
```

Hai câu về W21-A và W21-B đã cập nhật theo kết quả (C-246, 15/10 18:57). Các con số trong mục này đã được kiểm ở mục 8.

### 7.3 Các chỗ cần dọn (số dòng theo bản .tex hiện tại, 2157 dòng)

**Phần mở đầu và kết luận**

| Dòng | Hiện tại | Làm gì |
|---|---|---|
| 36–42 | Abstract: 6 dòng giới hạn (field, IDM, Salt Lake, "validated retrofit…", "small exactly solved models…") | Thay bằng câu cuối của abstract nháp (mục 5); phần còn lại chuyển sang 7.2 |
| 71 | "With Krauss human drivers on synthetic grids" | Xóa, cùng danh sách "eight things" (mục 9) |
| 78 | "qualitatively consistent … does not establish the adapter's necessity" | Xóa. **Đã lỗi thời**: W19 đã kiểm chính điều này |
| 80 | "transfer to other network builds is conditional" | Chuyển sang 7.2, mục Networks |
| 92–95 | Finding 7, "Field data bound the benefit" | Chuyển sang contribution 4 (Boundaries) và 7.2 |
| 108–109 | "with no single mediator isolated" | Sửa. **Mâu thuẫn** với VII-R |
| 110–111 | "(family-wise bound 0.075, conditional on each test holding its nominal level)" | Giữ "(chain bound 0.075)"; điều kiện chuyển sang 7.2, mục Inference |
| 114 | "without an isolated cause" | Chuyển sang 7.2 |
| 132–142 | Claim boundary | Thay bằng 7.2 (đặt cuối Discussion) và một câu trỏ tới đó ở cuối Intro |
| 1982–1983 | Conclusion: "without identifying every mediator" | Sửa. **Mâu thuẫn** |
| 1988–1991, 1994–1997 | Conclusion: Krauss, IDM, Salt Lake, field, "validated retrofit…" | Thay bằng một câu trỏ tới 7.2 |

**Methodology, Design và Formal**

| Dòng | Hiện tại | Làm gì |
|---|---|---|
| 226–227 | Small-gain: "motivation, not a theorem … none of these results' hypotheses is verified" | Rút còn "motivation only" |
| 512–513 | "The adapter does more than restore demand perception, so no single mediator is claimed" | Xóa. W19 thay thế câu này |
| 600–602 | Ghi chú budget/khởi tạo của port DC-Ada | Chuyển sang phụ lục bổ sung, cùng W7-2 |
| 826 | "asymmetric sensing-error scenario, not a universal robustness guarantee" | Chuyển sang 7.2, mục Channel and sensing |
| 863–868, 892–893, 916, 976–983, 994, 996–999 | Sáu lời nói lại phạm vi của các định lý | Giữ một đoạn ngắn (996–999); còn lại xóa |

**Results**

| Dòng | Hiện tại | Làm gì |
|---|---|---|
| 1026–1028, 1034–1037, 1043, 1047–1048 | M1: "Not RL; not compared…", "does not separate information from representation", "trace and intervention evidence…", "a fixed rule, not learned…" | Chuyển cả đoạn sang phụ lục (lịch sử M1) |
| 1072 | "warns of the trade-off but does not predict it" | Xóa |
| 1104–1105 | "they do not isolate a single mediator…" | Xóa. W19 thay thế câu này |
| 1112–1114 | "(including repeated calls…)", "(intervention evidence, not a measured loop gain or a stability proof)" | Rút còn một ngoặc đơn |
| 1128–1129, 1139–1141, 1192–1194, 1316–1317 | Caption bảng/hình mang lời rào đón (equivalence, "not every retraining method", "not an exhaustive ranking", reuse checkpoint) | Rút caption; nội dung chuyển sang 7.2 |
| 1165–1166 | "This does not overwrite… not zero-shot calibration or network transfer" | Xóa |
| 1183–1185 | "(not a claim about every forecaster without state)" | Xóa |
| 1228–1230, 1234–1236, 1241–1242, 1250–1259, 1272–1273, 1294–1297 | Rào đón về port DC-Ada/FoRL, H5, LCD | Chuyển sang phụ lục; thân bài giữ 1 đoạn tóm tắt |
| 1333–1335, 1341–1344, 1360–1363, 1381–1385, 1390–1395, 1422–1423 | Rào đón trong chẩn đoán spider/rand3 | Chuyển sang phụ lục; thân bài giữ 1 đoạn |
| 1564–1565 | "Scope of wave 13" | Xóa (đã có trong 7.2) |
| 1665–1666, 1692–1693, 1702 | Field: "none tests TSI", "one night hour…", "the performative effect … not present" | Giữ một câu "None tests TSI itself" |
| 1726–1728, 1736–1738 | W16–18: diễn giải kèm rào đón | Giữ con số; diễn giải chuyển sang 7.2 |
| 1797, 1810 | "our double DQN, not the libraries' learners" (lần 2), "neither policy was retrained" (lần 3) | Giữ một lần trong phương pháp W20 |
| 1826–1828, 1851–1853 | Midtown "Reading" | Chuyển sang 7.2, mục Networks |

**Discussion**

| Dòng | Hiện tại | Làm gì |
|---|---|---|
| 1857–1900 | "What the Results Establish" (842 chữ, nhắc lại kết quả kèm rào đón) | Thay bằng một bảng verdict H1–H5, mỗi giả thuyết một dòng (khoảng 150 chữ) |
| 1902–1955 | "Shortcomings and Limitations" (1.190 chữ) | Thay bằng 7.2 (khoảng 480 chữ) |

## 8. Đọc lại paper (10 lượt) và kiểm nháp

Mỗi lượt có một mục tiêu riêng; không phải đọc thẳng 10 lần như nhau. Chi tiết:

1. **Quét chủ đề trên toàn bộ 813 câu** (từ dòng 20 đến bibliography). Kết quả là bảng ở 7.1.
2. **Abstract, Intro, các đóng góp, Claim boundary, Conclusion** (dòng 20–147, 1980–1998), từng câu một: tách claim khỏi rào đón. Thấy 2 chỗ lỗi thời (dòng 78, 512) và 2 chỗ mâu thuẫn (dòng 108, 1982).
3. **Background và Gap** (dòng 150–243): đối chiếu với kết quả tìm collision hôm nay.
4. **Methodology và Design** (dòng 279–860): rào đón trong phần phương pháp (DC-Ada budget, sensing, small-gain).
5. **Formal** (dòng 862–999): phạm vi định lý bị nói lại sáu lần.
6. **Results M1–M3, comparators** (dòng 1003–1318).
7. **Results M4, W9, W13–W15** (dòng 1319–1663).
8. **Field, W16–18, Salt Lake, W19, W20, Midtown** (dòng 1664–1854).
9. **Discussion, Limitations, Open problems** (dòng 1856–1977): chỗ nào nhắc lại phần đã có ở trên.
10. **Kiểm từng con số và từng claim trong nháp** (mục 0–5 và 7.2), so với .tex, các report và ledger. Kết quả ở dưới.

**Kết quả kiểm nháp**

| Chỗ trong nháp | Kết luận | Đã sửa |
|---|---|---|
| §4, "+2.6 đến +16 s/veh" | **Sai một phần**: RL-H là +1.7, khoảng +2.6 đến +16 chỉ đúng cho các state của thư viện | Đã sửa |
| Abstract nháp, "isolates the cause" | **Quá mạnh**: feature học nào mang ngưỡng thì chưa cô lập | Sửa thành "identifies the cause as the stop threshold of the signal's inputs" |
| Abstract nháp, "defaults of sumo-rl and RESCO, under which…" | **Thiếu qualifier bắt buộc**: đọc như agent gốc của thư viện | Thêm "re-implemented and trained by our recipe" |
| Abstract nháp, "1.5–2.6 points more than fleet retraining" | **Mơ hồ** về mô hình: khoảng này là HBEFA4 (W13 −1.54/−1.56, W14-1 −1.66, W15-1 −2.64; PHEMlight5 W13 −1.64) | Thêm "(HBEFA4)"; abstract vẫn 250 chữ |
| Gap nháp, HONEST-CAV "observes lane queues" | **Chưa đủ**: state của họ còn có occupancy và speed; định nghĩa QLen chưa kiểm | Sửa thành "lane queue lengths (with occupancy and speed)"; vẫn ghi cần kiểm |
| §3, "Abstract khoảng 450 từ" | Đếm lại được **476 chữ** | Ghi nhận; kết luận không đổi |
| Contribution 1, "greens lengthen (11–30%)", "1.70 to 3.02 s" | Đúng (AH +11.4 %; thư viện 15/19/30 %; C-109) | — |
| "three of four families", "97%", "second attempt", "two fresh-policy replications" | Đúng (C-230: 16.02 → 0.51 = 96.8 %; C-118; W7-1, W8-2) | — |
| 7.2: 1.10 %, "none detectable" (P5 −0.31 [−1.01, +0.25]), "below 3%" (W18), +1.76 %, "six attempts" | Đúng | — |
| N5: "+1.79 % → −2.23 %" | Đúng (Table w13, cùng các hàng) | — |

## 9. Giảm độ dài

**Hiện tại:**
- 42 trang, khoảng 27.900 chữ phần text, 17 bảng, 8 hình.
- Trung bình khoảng 820 chữ mỗi trang, kể cả bảng.
- Bản cũ của Results chiếm khoảng 11.000 chữ; Discussion 2.380; Formal 2.010; Methodology 4.100; Intro 1.560.

**Mục tiêu:** thân bài khoảng 11.000 chữ (TR-C), cộng một file supplementary chứa chi tiết từng wave. Không bỏ kết quả nào: những gì rời thân bài đi vào supplementary, có số ledger.

| Mục | Chữ hiện tại → mục tiêu | Cách làm |
|---|---|---|
| Abstract | 476 → 250 | Bản nháp ở mục 5 |
| Intro | 1.560 → 800 | Bỏ danh sách "eight things" (trùng với contributions); 4 contributions; Claim boundary thành một câu trỏ |
| Background | 1.395 → 900 | Gộp "Compatibility" với "Observation adapters"; bỏ "Formal Statements" (48 chữ); viết lại Gap |
| Aims/RQ/H | 290 → 150 | Gộp RQ vào H1–H5 |
| Methodology | 4.100 → 2.200 | Giữ setting, populations, providers (ngắn), diagnostics (ngắn), TSI, TSI-G; comparators còn 1 đoạn (chi tiết sang supplementary); rút đoạn thống kê |
| Experimental design | 1.160 + 2 bảng lớn → 400 | Bảng tab:expmap (47 dòng) và tab:panels sang supplementary; giữ tab:nets |
| Formal | 2.010 → 700 | Giữ Thm 3 (one-car) và Thm 4 (queue) với chứng minh ngắn; Thm 1–2 sang phụ lục; Thm 5 (union bound) còn một câu |
| Results | 11.000 → 4.500 | Sắp lại theo thứ tự vấn đề → cơ chế → phạm vi → cách sửa → ranh giới (bảng dưới) |
| Discussion | 2.380 → 800 | Bảng verdict H1–H5, mục 7.2, Open problems còn 150 chữ |
| Conclusion | 350 → 180 | Không lặp giới hạn |
| Phụ lục A–D | 1.230 → supplementary | — |

**Results, từng mục:**

| Mục | Chữ hiện tại → mục tiêu | Cách làm |
|---|---|---|
| M1 | 550 → 150 | Tab:m1 rút gọn |
| M2 | 510 → 250 | Giữ fig:m2 |
| One-sided | 280 → 150 | — |
| Diagnosis | 310 → 300 | Giữ nguyên |
| Confirmation | Giữ tab:tsi và fig:mech | — |
| Replication | 320 → 200 | — |
| Scope | 210 → 150 | Gộp tab:allstats với fig:scope |
| Comparators | 1.610 → 300 | Giữ fig:comparators; tab:w6, tab:forlport và audit W7-2 sang supplementary |
| Networks | 1.890 → 400 | Tab:w10 và chẩn đoán spider sang supplementary |
| W9 + W14 robustness | 980 → 300 | Một bảng chung |
| W13 | 730 → 400 | Tab:w13modes sang supplementary |
| W15 | 925 → 250 | Giữ default và R15-U; 4 biến thể còn lại sang supplementary |
| Field | 750 → 400 | — |
| W16–18 | 440 → 250 | — |
| Salt Lake | 280 → 150 | — |
| W19 | 440 → 400 | Lõi, giữ |
| W20 | 390 → 400 | Lõi, giữ |
| Midtown | 650 → 300 | — |
| W21 (mới) | → 300 | — |

**Ước tính:**
- Thân bài khoảng 10.900 chữ, 7 bảng, 6 hình.
- Ở định dạng hai cột IEEE hiện tại, khoảng 16–18 trang, so với 42 trang bây giờ.

**Nếu chỉ muốn cắt nhanh, không đổi cấu trúc** (khoảng −6.500 chữ, còn khoảng 27 trang):
1. Bảng verdict thay "What the Results Establish", và 7.2 thay "Limitations": −1.500.
2. Bỏ "eight things": −700.
3. Thm 1, 2, 5 sang phụ lục: −900.
4. Bảy bảng phụ sang supplementary (expmap, panels, forlport, w6, w10, w15, w13modes): khoảng −3 trang.
5. Chi tiết comparators: −1.200.
6. Chẩn đoán spider/rand3: −1.200.
7. Lịch sử M1: −350.
8. Các biến thể W15: −600.
