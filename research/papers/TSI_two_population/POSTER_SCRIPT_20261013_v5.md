# Poster TSI, bản v5 (13/10/2026): kịch bản thuyết trình và những điều cần biết

**File poster:**
- Bản in: `research/papers/TSI_two_population/TSI_poster_v5.pdf`, khổ 16:9, ảnh không nén.
- Bản sửa được: `TSI_poster_v5.pptx`.
- Dựng lại bằng `bash scripts/POSTER_tsi_v5_build.sh`.
- Bản v4 (09/10, bản đã đăng LinkedIn) và kịch bản v4 giữ nguyên, không bị sửa.
- Lý do sửa: báo cáo review `research/papers/audits/POSTER_TSI_V4_REVIEW_20261013.md`.

**Nguyên tắc của bản này:**
- Giọng văn vẫn nêu thành tựu.
- Mọi câu trên poster phải đúng theo chính luật quyết định đã ghi trên poster.
- Giới hạn quan trọng nhất (mô hình tài xế) nay nằm trên poster, mục Limitations.
- Các sự thật còn lại vẫn ở Phần 6, để trả lời khi được hỏi.

---

## Phần 0. v5 đổi gì so với v4, và vì sao

| Chỗ trên poster | v4 | v5 | Vì sao |
|---|---|---|---|
| TSI-G (Results) | "repairs the community defaults" | "removes over 95% of the harm"; −0.2, −0.2 (đạt giới hạn), 0.5 (ngay trên giới hạn) | MPLight +0.51, cận trên +0.74 > +0.5: không đạt luật đăng ký (C-230) |
| Why (Introduction) | "A car gliding on SPaT never counts" | "never enters these queue, waiting or pressure counts" | sumo-rl có density (đếm mọi xe); RESCO drq có số xe đang tới và tổng tốc độ |
| Khuyến nghị cho thành phố | "speed or position inputs work with the forecast alone" | "any stop-based input needs TSI or TSI-G, even beside speed or density" | RESCO IDQN có đầu vào tốc độ mà vẫn bị hại 2.6 s |
| The repair works | "transfers to two more networks, tolerates 80% detection" | "tolerates a 1-s delay, 20–50% message loss and speed noise; recalibrated, TSI passed on a second network and a two-lane build of a third" | Chuyển giao dùng hiệu chỉnh lại, không phải bản mặc định; 80% phát hiện chạm biên +0.56 (C-184) |
| Nhiên liệu TSI-G | "5–10% fuel saved" | "5–10% (HBEFA4; 3–6% PHEMlight5)" | Cột PHEMlight5 trên chính Fig. 3B chỉ 2.8–5.6% |
| −3.85% | không ghi mô hình nhiên liệu | "(HBEFA4; …)" | Cùng thiết kế đó +1.76% dưới PHEMlight5 (C-142) |
| Fig. 3 | trục "extra wait", nhóm "counts only stopped cars" | trục "extra delay", nhóm "stop-based inputs", có vạch giới hạn +0.5 | Số vẽ là time loss; nhãn nhóm sai với sumo-rl / IDQN |
| Limitations | "Calibrated simulation" | "Simulation with SUMO's default drivers: against drivers matched to NGSIM trajectories the fleet saves about 1% fuel (HBEFA4), none detectable under PHEMlight5, so the robust result is the time effect" | W17 (C-218), W18 (C-223); paper ghi "Field data bound the benefit" |
| Checked against field data | "the fleet saves about 10% fuel" | "about 10% against human drivers, and the upgrade did not break it" | Ở Salt Lake, M1 so với tài xế người; nâng cấp không làm hỏng đội xe (C-217) |
| MaxPressure | "MaxPressure counts vehicles at every speed" | "Varaiya's MaxPressure …" | MaxPressure của RESCO dùng pressure từ xe dừng |
| We pinpoint the cause | "any scale constant" | "scale constants halved or doubled" | Chỉ thử ×½, ×2 |
| TSI-G trên RL-H | "beats TSI (−0.3 s/veh)" | bỏ khỏi poster | Xe người chậm thêm 0.57 s so với TSI |
| DC-Ada / FoRL | "ported" | "our ports of" | Đó là bản port của mình |
| Fig. 1 | không giải thích nhãn | giải thích R9, R10, rule, spider | Người đọc không hiểu ký hiệu nội bộ |
| Fig. 4 | không nói thiết kế | "(B, first TSI attempt)" | Panel B vẽ thiết kế TSI đầu tiên (adapter chung) |
| Công thức hàng đợi | màu đỏ sẫm, ký hiệu chưa định nghĩa | màu mực như các công thức khác; λ, ρ, A, θ định nghĩa trong câu | Thống nhất trình bày |
| Dòng NSF | dấu * không có chỗ tham chiếu | bỏ dấu * | |
| Tài liệu tham khảo | [10], [11] dùng ngoặc kép thẳng | ngoặc kép cong như các mục khác | |
| Metadata | không có (tiêu đề "PowerPoint Presentation") | tiêu đề, tác giả, chủ đề | |

**Không đổi:**
- Bố cục và cỡ chữ.
- Hình 1, 2, 4.
- Tiêu đề poster, tác giả, mentor, dòng NSF.

**Về kích thước hình:**
- Fig. 1 và Fig. 2 giữ nguyên kích thước v4.
- Fig. 3 rộng 2.50 in (v4: 2.64).
- Fig. 4 rộng 1.99 in (v4: 2.38), vì chữ đính chính dài hơn.

---

## Phần 1. Số liệu cần thuộc (đều có trên poster)

| Điều | Số |
|---|---|
| Đội xe tiết kiệm dưới đèn cố định (tài xế mặc định của SUMO) | 6.5% nhiên liệu |
| Với tài xế khớp quỹ đạo NGSIM | khoảng 1% (HBEFA4), không đo được dưới PHEMlight5 |
| TSI, xác nhận đã đăng ký | −3.85% nhiên liệu (HBEFA4; 95% CI 3.26–4.43), mọi time loss trong giới hạn |
| TSI mặc định trên đèn và đội xe mới | −5.6% (HBEFA4), −3.3% (PHEMlight5) |
| Độ bền của bản mặc định | trễ 1 s, mất 20–50% tin, nhiễu tốc độ: vẫn đạt |
| Chỉ công bố dự báo, đèn RL-H | xe đội chậm thêm 1.7 s/xe |
| sumo-rl mặc định / RESCO IDQN / RESCO MPLight, chỉ dự báo | +5.4 / +2.6 / +16.0 s/xe |
| Có TSI-G | −0.2 / −0.2 (đạt giới hạn) / +0.5 (ngay trên giới hạn); tiết kiệm 5–10% (HBEFA4), 3–6% (PHEMlight5) |
| Đèn không có đầu vào ngưỡng dừng (speed groups / queue positions / RESCO wave), chỉ dự báo | −0.4 / −0.4 / −1.0 s/xe, không cần sửa |
| MaxPressure (Varaiya), chỉ dự báo, đăng ký trước | đạt mọi giới hạn, −2.68% nhiên liệu |
| Thực địa | Hamburg: dự báo giữ đúng quantile 0.1 trên ngày chưa thấy; Salt Lake City: đội xe tiết kiệm khoảng 10% so với tài xế người |
| Chuyển giao (hiệu chỉnh lại) | rand3 −2.17%; spider bản hai làn −1.49% |
| Thiết kế thí nghiệm | 5 đèn × 4 đội xe × 20 seed giao thông mới; bootstrap chéo; luật quyết định chốt trước |

---

## Phần 2. Pitch 30 giây (học thuộc)

> Traffic lights and connected cars are both becoming AI, and they are owned and upgraded by different people. We found that when cars use the light's timing to glide instead of stopping, a learned traffic light whose inputs count stopped cars serves them later. Those stop counts are in the defaults of the two most used open-source libraries. We fix it without retraining either AI: the cars get a calibrated forecast, and the light senses each connected car as the human driver it replaces. The extra delay almost disappears, and the fleet keeps a fuel saving.

*Nghĩa:* Đèn và xe kết nối đều thành AI, do những bên khác nhau sở hữu và nâng cấp. Khi xe dùng thông tin thời gian đèn để lướt thay vì dừng, đèn học có đầu vào đếm xe dừng sẽ phục vụ chúng muộn hơn. Các đầu vào đếm xe dừng đó nằm trong mặc định của hai thư viện mã nguồn mở phổ biến nhất. Chúng tôi sửa mà không huấn luyện lại AI nào: xe được báo một dự báo đã hiệu chỉnh, còn đèn cảm nhận mỗi xe kết nối như chiếc xe người lái mà nó thay thế. Phần chậm thêm gần như biến mất, và đội xe vẫn tiết kiệm nhiên liệu.

---

## Phần 3. Đi qua poster trong 2 phút (học thuộc; [ngoặc vuông] = chỉ tay vào đâu)

**1. Bối cảnh, khoảng 20 s** [chỉ Fig. 1]
> Every stop at a red light wastes fuel. If the light broadcasts when it will turn green, connected cars can ease off early and glide through. In our simulation an AI eco-driving fleet saves six and a half percent fuel this way under fixed-time lights. But once the lights themselves become AI-controlled, that saving disappears.

**2. Nguyên nhân, khoảng 25 s** [chỉ Fig. 2]
> Here is why. Most learned lights count a car as waiting only once it has stopped, below 0.1 meters per second. That is in the defaults of sumo-rl and RESCO. A car that glides never enters those queue or waiting counts, so the light holds the other green longer, and the gliding cars arrive at a red light anyway. The forecast defeats itself.

**3. Cách sửa, khoảng 25 s** [chỉ cột giữa: Fleet side, Light side, TSI-G]
> We keep both AIs frozen and change only two interfaces. On the car side, a forecast calibrated on the deployed light's own logs. On the light side, TSI counts gliding cars, and its general form, TSI-G, senses each connected car as the human driver it replaces. Every count the light uses is then computed on those twins.

**4. Kết quả, khoảng 35 s** [chỉ Fig. 3]
> This is the main result. Orange is the forecast alone; blue is with our repair; the dashed line is our limit. Every light with stop-based inputs makes the cooperating cars wait longer: almost two seconds per vehicle for ours, five for the sumo-rl default, sixteen for RESCO's MPLight. With the repair the extra delay is gone for three of them, without retraining; on MPLight it drops from sixteen seconds to half a second, just above our strict limit. The fleet saves five to ten percent fuel under one emission model, three to six under the other. On the right, the control: lights with no stop-based input never needed a repair, as our model predicted.

**5. Kiểm chứng, giới hạn và kết luận, khoảng 20 s** [chỉ "Checked against field data", "Limitations", "Conclusions"]
> We checked the pieces against field data: the forecaster on real adaptive signals in Hamburg, the fuel models against measured fuel, and recorded demand from Salt Lake City. One honest limit: with drivers matched to real trajectories the fuel saving gets small, about one percent, so the robust result is the time effect. The lesson for cities: before deploying a learned light where cars use SPaT, check what it counts.

---

## Phần 4. Câu hỏi thường gặp (trả lời ngắn, tiếng Anh)

**Q1. Did you create the problem by choosing a halting-count signal?**
> We tested exactly that. Stop-based counts are in the defaults of sumo-rl and of RESCO's IDQN, IPPO and MPLight, and with those defaults the harm is larger than with ours: 2.6 to 16 seconds per vehicle. Retrained by the same recipe with no stop-thresholded input (speed groups, positions, or RESCO's wave state), there was no harm at all.

**Q2. sumo-rl also uses density, and RESCO's IDQN state uses speeds. Why are they harmed?**
> Because they also contain stop-thresholded features: queue, waiting time, pressure. The learned policies rely on those, so a gliding car still counts less. Having speed or density next to them is not enough.

**Q3. What exactly is the human twin?**
> For each connected car we compute where a human driver would be: driving at its free speed from where it entered the lane, braking, following the car ahead, stopping at the back of the queue, and starting after the car in front moves. The light's counts use that twin instead of the gliding car.

**Q4. What information does TSI-G need?**
> Which cars follow SPaT, which the infrastructure knows through V2X, and one parameter, how long a driver rolls before stopping, calibrated on ordinary traffic logs. The twins reproduce human stopped time within two percent.

**Q5. Why not just retrain the light?**
> Lights and cars are owned by different parties and upgraded on different schedules, so retraining needs both sides together. Our fix works on the frozen systems. And for a new light, our results say: avoid stop-thresholded inputs.

**Q6. How big is the fuel benefit really?**
> With SUMO's default drivers, five to ten percent. With drivers matched to real trajectories from NGSIM, about one percent, and nothing detectable under the emission model that measured fuel favours. So we lead with the time effect, which does not depend on that.

**Q7. How do you know the results are not luck?**
> Every decision rule was registered before the confirmation run: five independently trained signals, four fleets, twenty fresh traffic seeds, and a crossed bootstrap over all three. Self-checks recompute every input independently.

**Q8. What is the theorem for?**
> It predicted the result before we ran it: a light that counts slow cars as waiting needs no light-side change, and each one-sided fix fails alone. MaxPressure and the lights with no stop threshold confirmed it.

**Q9. What is new compared with prior work?**
> Earlier work fixes one side: better forecasts, smarter cars, or retraining. We show that the two AIs interact through what the light counts, and we repair that interaction without retraining either one.

**Q10. What's next?**
> A road pilot with a SPaT-equipped fleet, more fleet shares and networks, and the libraries' own learners.

---

## Phần 5. Mẹo trình bày
- Mở bằng pitch 30 giây, rồi hỏi người nghe muốn nghe chi tiết hay không.
- Khi nói kết quả, **luôn chỉ vào Fig. 3**: cam là chỉ dự báo, xanh là có sửa, vạch đứt là giới hạn, bên phải là đối chứng.
- Nói thẳng chuyện MPLight ("half a second, just above our limit"). Đừng nói "repairs all".
- Nếu không biết câu trả lời: "Good question; we haven't tested that yet, it's on our list."

---

## Phần 6. Những sự thật cần biết (chỉ dùng khi được hỏi)

| # | Sự thật | Nếu bị hỏi, trả lời |
|---|---|---|
| 1 | **Mô hình tài xế** (nay đã ghi trên poster, Limitations): W17 cho ra khoảng 1% / 0 với tài xế khớp NGSIM. W18 thử 5 kiểu thiết kế đội xe, không kiểu nào đạt ≥3% dưới cả hai mô hình; tốt nhất là "không bò" −0.9% / −2.5%. | Xem Q6. |
| 2 | **Thiết kế TSI ban đầu** (q0.5, chỉnh (A, B) từng đèn) tiết kiệm dưới HBEFA4 nhưng tốn thêm 1.76% dưới PHEMlight5. Con số −3.85% trên poster là của thiết kế này, dưới HBEFA4. Bản mặc định (q0.1, (1, 0.25)) tiết kiệm dưới cả hai. | "The first registered design did not hold under PHEMlight5; the default setting does." |
| 3 | **Mỗi nửa riêng lẻ đều thất bại:** chỉ dự báo thì xe đội bị chậm; chỉ adapter thì không tiết kiệm nhiên liệu. | "Yes, each half alone fails, as the theorem predicts; that's why it's two-sided." |
| 4 | **MPLight:** +0.51 s/xe [0.30, 0.71], cận trên đăng ký +0.74 > +0.5, nên NOT SHOWN (nay đã ghi trên poster). | "Half a second, just above our strict limit, so we count it as not passed, though the harm fell from sixteen seconds." |
| 5 | **Chuyển giao:** spider một làn trượt 4 lần đăng ký; chỉ bản dựng lại hai làn mới qua, với (1, 0.5). rand3 qua ở lần thứ hai sau khi mở rộng dải adapter (chain bound 0.075). | "One single-lane network failed; with two lanes it passed. Single-lane roads with following traffic remain open." |
| 6 | **Độ bền:** bản mặc định chịu trễ 1 s (−3.29%), mất 20% tin (−3.66%), mất 50% tin (−1.88%) và nhiễu tốc độ (−4.60%). Với 80% phát hiện thì tiết kiệm −4.76% nhưng thời gian xe đội chạm biên (+0.56). Bản TSI cũ thì yếu với trễ 1 s (còn −0.74%). | "Delay and message loss are fine for the default; with only 80% of cars detected the fleet's time reaches our limit." |
| 7 | **Đối thủ:** port DC-Ada tiết kiệm nhiên liệu tương đương nhưng xe đội chậm thêm 2.2 s/xe; port FoRL tiết kiệm 0.70% nhưng chậm thêm 0.52 s/xe. | "We ported them to our task; they save fuel but cost the fleet time beyond our limit. They are our ports, not the authors' code." |
| 8 | **Đầu vào ngưỡng dừng là mặc định** của sumo-rl và RESCO (W20), nên vấn đề không phải do mình tự tạo ra. | Xem Q1, Q2. |
| 9 | **Reward:** reward không dùng ngưỡng (độ trễ) làm tác hại giảm còn một nửa (+0.85 so với +1.70 s/xe), nhưng vẫn cần sửa. | "The reward's threshold accounts for about half; the input's threshold is the main cause." |
| 10 | **Hằng số** 10/20/60 và hệ số chia reward 10 là số tròn chọn tay. Đã thử ÷2, ×2, và reward /1, /100: tác hại và cách sửa giữ nguyên. | "Halving, doubling or rescaling them changes nothing." |
| 11 | **Biểu diễn benchmark** (sumo-rl, RESCO) được **cài lại** và huấn luyện bằng **DQN của mình**, không phải learner gốc (pfrl). | "We used the libraries' state and reward definitions with our own learner." |
| 12 | **Thuần mô phỏng:** mạng tổng hợp (grid4, rand3, spider) và một hành lang Salt Lake City với nhu cầu ghi thật. | "It's simulation, with the components checked against field data; a road pilot is next." |
| 13 | **Salt Lake City:** nâng cấp lên đèn học giàu đầu vào **không làm đội xe mất lợi ích**, nên không có gì để TSI cứu; ở đó TSI còn kém lịch cũ. | "On Salt Lake demand the richer light did not break the fleet, consistent with our finding." |
| 14 | **Tài xế IDM:** thiết kế TSI cố định không giữ được khi mọi xe dùng IDM (W9-4, W16). | "Under a different car-following model the frozen design needs recalibration." |
| 15 | **Tỷ lệ đội xe:** TSI gốc ở 75% xe là đội: −4.75%, trong giới hạn. Ở 25%: −4.13%, nhưng thời gian xe đội sát biên, không vững. | "At 75% fleet share it held; at 25% it was at the margin." |
| 16 | **Lần xác nhận TSI đầu tiên** (adapter chung, C-114): nhiên liệu −4.56% nhưng xe đội chậm thêm +0.85 s/xe, trượt giới hạn. Panel B của Fig. 4 vẽ chính thiết kế này. | "The first registered attempt saved more fuel but cost the fleet time; the second met every limit." |
| 17 | **Checkpoint dùng lại:** −3.85% trên các panel dùng lại checkpoint; với policy mới hoàn toàn TSI tiết kiệm −2.61%. | "With freshly trained policies the saving was smaller, 2.6%, and the two-sided result replicated." |
| 18 | **TSI-G trên RL-H** tốt hơn TSI về thời gian xe đội (−0.32 s/xe) nhưng xe người chậm hơn TSI 0.57 s/xe; so với không có SPaT thì xe người vẫn không chậm (−0.08). | "TSI-G shifts a little time from human cars to the cooperating cars, compared with TSI; against no SPaT nobody waits longer." |
| 19 | **RESCO wave:** TSI-G cho kết quả trùng hệt chỉ dự báo, vì bản sao không đổi số xe trên làn. | "Where the light already counts every car, TSI-G changes nothing, so it is safe to deploy everywhere." |
| 20 | **Dưới PHEMlight5, bản sửa đổi một ít nhiên liệu lấy thời gian:** RL-H chỉ dự báo −4.41%, với TSI −3.25%; IDQN −4.22% → −2.83%. | "The forecast alone already saves fuel but costs the fleet time; the repair buys the time back, at a small fuel cost under PHEMlight5." |
