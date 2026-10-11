# Poster TSI, bản 09/10/2026: kịch bản thuyết trình và những điều cần biết

**File poster:**
- Bản in: `research/papers/TSI_two_population/TSI_poster_v4.pdf`, giữ nguyên độ phân giải ảnh, khổ 16:9.
- Bản sửa được: `TSI_poster_v4.pptx`.
- Dựng lại bằng `bash scripts/POSTER_tsi_v4_build.sh`.
- Bản gốc của anh/chị (06/10) vẫn ở thư mục gốc repo, không bị sửa.

**Nguyên tắc của bản này:**
- Poster chỉ nêu **thành tựu**.
- Các giới hạn, kết quả âm và cách chọn luật/hằng số **không ghi trên poster**, nhưng gom đủ ở **Phần 6** của file này, để anh/chị nắm và trả lời khi có người hỏi.
- Mọi con số trên poster đều đúng với dữ liệu đã đăng ký.

---

## Phần 0. Poster đã đổi gì so với bản 06/10, và vì sao

- **Giữ nguyên câu văn của anh/chị** ở mọi chỗ vẫn đúng: Context, Related Work, Testbed, Fleet side, Decision, lý thuyết, "A prediction made before the run held", Bottom line.
- **Sửa những câu nay đã sai:**
  - "(A, B) tuned per signal, 52 episodes": giờ đã có một cài đặt mặc định (1, 0.25) dùng được cho đèn mới, không cần chỉnh từng đèn.
  - "about three-fifths of the benefit comes back": con số này của thiết kế cũ, chỉ dưới HBEFA4. Thay bằng kết quả của bản mặc định: −5.6% (HBEFA4) và −3.3% (PHEMlight5).
  - "though the learned signals are not threshold rules": W19 chứng minh chính ngưỡng dừng gây ra vấn đề.
  - Câu "becomes a 1.76% fuel increase with PHEMlight5" trong Limitations: chỉ đúng với thiết kế cũ; bản mặc định tiết kiệm dưới cả hai mô hình.
- **Thêm thành tựu mới:**
  - "Why": ngưỡng 0.1 m/s là mặc định của sumo-rl và RESCO.
  - TSI-G: một lớp cảm biến dùng được cho mọi đèn.
  - "We pinpoint the cause" (W19).
  - "TSI-G repairs the community defaults" (W20).
  - "Checked against field data" (Hamburg, VED, Salt Lake).
  - Fig. 3 mới: ai phải trả giá, và bản sửa.
- **Tác giả:** "Vu Phan An Nguyen", dòng dưới "Mentor: Dr. Jay Zhengping Luo".
- **Kỹ thuật in:**
  - Ảnh Fig. 1, 2, 4 vẽ lại 600 dpi từ PDF gốc.
  - PDF xuất **không nén ảnh**. Chế độ mặc định nén ảnh xuống khoảng 62 dpi khi in khổ 48 in.
  - Ba cột thẳng hàng, không tràn, không chồng chữ; đề mục cùng cỡ và căn giữa.

---

## Phần 1. Số liệu cần thuộc (đều có trên poster)

| Điều | Số |
|---|---|
| Đội xe tiết kiệm dưới đèn cố định (mô phỏng) | 6.5% nhiên liệu |
| TSI, xác nhận đã đăng ký | −3.85% nhiên liệu (95% CI 3.26–4.43), mọi time loss trong giới hạn |
| TSI mặc định trên đèn và đội xe mới | −5.6% (HBEFA4), −3.3% (PHEMlight5) |
| Chỉ công bố dự báo, đèn RL-H | xe đội chờ thêm 1.7 s/xe |
| sumo-rl mặc định / RESCO IDQN / RESCO MPLight, chỉ dự báo | +5.4 / +2.6 / +16.0 s/xe |
| Có TSI-G | −0.2 / −0.2 / +0.5 s/xe; tiết kiệm 5–10% nhiên liệu |
| Đèn thấy tốc độ / vị trí / mọi xe (RESCO wave), chỉ dự báo | −0.4 / −0.4 / −1.0 s/xe (không bị hại), không cần sửa |
| TSI-G trên RL-H (đèn của paper) | −0.3 s/xe, tốt hơn TSI gốc 0.3 s/xe; đạt mọi giới hạn |
| MaxPressure, chỉ dự báo (đăng ký trước) | đạt mọi giới hạn, −2.68% nhiên liệu |
| Thực địa | Hamburg: dự báo giữ đúng quantile 0.1 trên ngày chưa thấy; Salt Lake City: đội xe tiết kiệm khoảng 10% |
| Chuyển giao / độ bền | mạng thứ hai −2.17%, bản hai làn của mạng thứ ba −1.49%; chịu được 80% phát hiện và 20% mất tin |
| Thiết kế thí nghiệm | 5 đèn × 4 đội xe × 20 seed giao thông mới; bootstrap chéo; luật quyết định chốt trước |

---

## Phần 2. Pitch 30 giây (học thuộc)

> Traffic lights and connected cars are both becoming AI, and they are owned and upgraded by different people. We found that when cars use the light's timing to glide instead of stopping, a learned traffic light that counts only stopped cars stops seeing them and serves them later. This is the default design in the two most used open-source libraries. We fix it without retraining either AI: the cars get a calibrated forecast, and the light senses each connected car as the human driver it replaces. The cars keep their fuel savings, and nobody waits longer.

*Nghĩa:* Đèn và xe kết nối đều thành AI, do những bên khác nhau sở hữu và nâng cấp. Khi xe dùng thông tin thời gian đèn để lướt thay vì dừng, đèn học chỉ đếm xe dừng sẽ không thấy chúng và phục vụ chúng muộn hơn. Đây là thiết kế mặc định của hai thư viện mã nguồn mở phổ biến nhất. Chúng tôi sửa mà không huấn luyện lại AI nào: xe được báo một dự báo đã hiệu chỉnh, còn đèn cảm nhận mỗi xe kết nối như chiếc xe người lái mà nó thay thế. Xe giữ được phần nhiên liệu tiết kiệm, và không ai phải chờ lâu hơn.

---

## Phần 3. Đi qua poster trong 2 phút (học thuộc; [ngoặc vuông] = chỉ tay vào đâu)

**1. Bối cảnh, khoảng 20 s** [chỉ Fig. 1]
> Every stop at a red light wastes fuel. If the light broadcasts when it will turn green, connected cars can ease off early and glide through. In our simulation an AI eco-driving fleet saves six and a half percent fuel this way under fixed-time lights. But once the lights themselves become AI-controlled, that saving disappears.

*Nghĩa:* Mỗi lần dừng đèn đỏ là tốn nhiên liệu. Nếu đèn phát khi nào sẽ xanh, xe có thể nhả ga sớm và lướt qua. Trong mô phỏng, đội xe AI tiết kiệm 6.5% nhiên liệu dưới đèn cố định. Nhưng khi đèn thành AI, khoản tiết kiệm đó biến mất.

**2. Nguyên nhân, khoảng 25 s** [chỉ Fig. 2]
> Here is why. Most learned lights count a car as waiting only once it has stopped, below 0.1 meters per second. That is the default in sumo-rl and RESCO. A car that glides never counts, so the light thinks the approach is empty, holds the other green longer, and the gliding cars arrive at a red light anyway. The forecast defeats itself.

*Nghĩa:* Lý do: hầu hết đèn học chỉ coi xe là đang chờ khi xe đã dừng hẳn, dưới 0.1 m/s; đó là mặc định của sumo-rl và RESCO. Xe lướt không bao giờ được đếm. Đèn tưởng hướng đó trống, giữ pha xanh kia lâu hơn, và xe lướt vẫn đến lúc đèn đỏ. Dự báo tự phá chính nó.

**3. Cách sửa, khoảng 25 s** [chỉ cột giữa: Fleet side, Light side, TSI-G]
> We keep both AIs frozen and change only two interfaces. On the car side, a forecast calibrated on the deployed light's own logs. On the light side, TSI counts gliding cars, and its general form, TSI-G, senses each connected car as the human driver it replaces: where that car would be, and whether it would be stopped, if a person were driving. Every count the light uses is then computed on those twins.

*Nghĩa:* Giữ nguyên cả hai AI, chỉ đổi hai giao diện. Phía xe: một dự báo hiệu chỉnh trên log của chính đèn đang chạy. Phía đèn: TSI đếm cả xe đang lướt; dạng tổng quát TSI-G cảm nhận mỗi xe kết nối như chiếc xe người lái nó thay thế (xe đó sẽ ở đâu, có đang dừng không nếu người lái), rồi tính mọi đại lượng đèn dùng trên các bản sao đó.

**4. Kết quả, khoảng 35 s** [chỉ Fig. 3]
> This is the main result. Orange is the forecast alone; blue is with our repair. Every light that counts only stopped cars makes the cooperating cars wait longer: almost two seconds per vehicle for ours, five for the sumo-rl default, sixteen for RESCO's MPLight. With TSI or TSI-G that extra wait is essentially gone, without retraining, and the fleet saves five to ten percent fuel. On the right of panel A, the control: lights that see speed or position never needed a repair, which is exactly what our model predicted.

*Nghĩa:* Đây là kết quả chính. Cam là chỉ dự báo, xanh là có bản sửa. Mọi đèn chỉ đếm xe dừng đều làm xe hợp tác chờ lâu hơn: gần 2 s/xe với đèn của chúng tôi, 5 s với sumo-rl, 16 s với MPLight của RESCO. Có TSI hoặc TSI-G thì phần chờ thêm gần như biến mất, không cần huấn luyện lại, và đội xe tiết kiệm 5–10% nhiên liệu. Bên phải panel A là đối chứng: đèn thấy tốc độ hoặc vị trí không cần sửa, đúng như mô hình dự đoán.

**5. Kiểm chứng và kết luận, khoảng 15 s** [chỉ "Checked against field data", "Conclusions"]
> We also checked the pieces against field data: the forecaster on real adaptive signals in Hamburg, fuel models against measured fuel, and recorded demand from Salt Lake City, where the fleet saves about ten percent. The lesson for cities: before deploying a learned light where cars use SPaT, check what it counts.

*Nghĩa:* Chúng tôi cũng kiểm chứng các thành phần bằng dữ liệu thực địa: bộ dự báo trên đèn thích ứng thật ở Hamburg, mô hình nhiên liệu so với nhiên liệu đo được, và nhu cầu thật của Salt Lake City (đội xe tiết kiệm khoảng 10%). Bài học cho thành phố: trước khi triển khai đèn học ở nơi xe dùng SPaT, hãy kiểm tra đèn đếm cái gì.

---

## Phần 4. Câu hỏi thường gặp (trả lời ngắn, tiếng Anh)

**Q1. Did you create the problem by choosing a halting-count signal?**
> We tested exactly that. Stop-based counts are the default in sumo-rl and in RESCO's IDQN, IPPO and MPLight, and with those defaults the harm is larger than with ours: 2.6 to 16 seconds per vehicle. When we retrained by the same recipe with speed or position inputs, or with RESCO's wave state that counts every vehicle, there was no harm at all.

**Q2. What exactly is the human twin?**
> For each connected car we compute where a human driver would be: driving at its free speed from where it entered the lane, braking, following the car ahead, stopping at the back of the queue, and starting after the car in front moves. The light's counts use that twin instead of the gliding car.

**Q3. What information does TSI-G need?**
> Which cars follow SPaT, which the infrastructure already knows through V2X, and one parameter, how long a driver rolls before stopping, calibrated on ordinary traffic logs. The twins then reproduce human stopped time within two percent.

**Q4. Why not just retrain the light?**
> Lights and cars are owned by different parties and upgraded on different schedules, so retraining needs both sides together. Our fix works on the frozen systems. And for a new light, our results say: give it speed or position inputs.

**Q5. How do you know the results are not luck?**
> Every decision rule was registered before the confirmation run: five independently trained signals, four fleets, twenty fresh traffic seeds, and a crossed bootstrap over all three. Self-checks recompute every input independently.

**Q6. Why two fuel models?**
> HBEFA4 and PHEMlight5 treat gliding differently; measured fuel data favour PHEMlight5, and our default repair saves fuel under both.

**Q7. What is the theorem for?**
> It predicted the result before we ran it: a light that counts slow cars as waiting needs no light-side change, and each one-sided fix fails alone. MaxPressure and the speed- or position-based lights confirmed it.

**Q8. What is new compared with prior work?**
> Earlier work fixes one side: better forecasts, smarter cars, or retraining. We show that the two AIs interact through what the light counts, and we repair that interaction without retraining either one.

**Q9. What's next?**
> A road pilot with a SPaT-equipped fleet, more fleet shares and networks, and the libraries' own learners.

---

## Phần 5. Mẹo trình bày
- Mở bằng pitch 30 giây, rồi hỏi người nghe muốn nghe chi tiết hay không.
- Khi nói kết quả, **luôn chỉ vào Fig. 3**: cam là chỉ dự báo, xanh là có sửa, bên phải là đối chứng.
- Nếu không biết câu trả lời: "Good question; we haven't tested that yet, it's on our list."
- Chỉ đưa ra các sự thật ở Phần 6 **khi được hỏi đúng chỗ**, và trả lời ngắn, thẳng thắn.

---

## Phần 6. Những sự thật cần biết (KHÔNG có trên poster; chỉ dùng khi được hỏi)

| # | Sự thật | Nếu bị hỏi, trả lời |
|---|---|---|
| 1 | **Lợi ích nhiên liệu phụ thuộc mô hình tài xế.** Với tài xế mặc định Krauss, đội xe tiết kiệm 6.5%. Với tài xế hiệu chỉnh từ dữ liệu thật (NGSIM), đội xe chỉ tiết kiệm khoảng 1% (HBEFA4), gần 0 dưới PHEMlight5 (W17). Thử 5 kiểu thiết kế đội xe khác (W18), không kiểu nào đạt ≥3% dưới cả hai mô hình; tốt nhất là "không bò" −0.9% / −2.5%. | "The size of the fuel saving depends on the driver model. With drivers calibrated on real trajectories it is smaller, around one percent in queued traffic, so we emphasise the time and fairness effect, which does not depend on that." |
| 2 | **Thiết kế TSI ban đầu** (q0.5, chỉnh (A, B) từng đèn) tiết kiệm dưới HBEFA4 nhưng tốn thêm 1.76% dưới PHEMlight5. Bản mặc định sau này (q0.1, (1, 0.25)) mới tiết kiệm dưới cả hai. | "The first version did not hold under PHEMlight5; the default setting we show does." |
| 3 | **Mỗi nửa riêng lẻ đều thất bại:** chỉ dự báo thì xe đội bị chậm; chỉ adapter thì không tiết kiệm nhiên liệu. Đây là điều định lý dự đoán. | "Yes, each half alone fails, as the theorem predicts; that's why it's two-sided." |
| 4 | **TSI-G trên RESCO MPLight:** +0.51 s/xe [0.30, 0.71], **vượt nhẹ giới hạn +0.5** nên kiểm định đăng ký **không đạt** (dù đã giảm từ 16 s). Với sumo-rl và RESCO IDQN thì đạt (α 0.0125). | "On MPLight the remaining wait is half a second, just above our strict 0.5 limit, so we count it as not passed, even though the harm dropped from sixteen seconds." |
| 5 | **Chuyển giao:** mạng spider một làn **thất bại 4 lần đăng ký**; chỉ bản dựng lại hai làn mới qua. rand3 cần nới dải adapter. | "One single-lane network failed; with two lanes it passed. Single-lane roads with following traffic remain open." |
| 6 | **Độ bền:** SPaT trễ từ 1 s trở lên làm phần tiết kiệm giảm còn 0.74%. | "Latency matters: answers one second stale cut the saving to under one percent." |
| 7 | **Đối thủ:** DC-Ada port tiết kiệm nhiên liệu tương đương nhưng xe đội chậm thêm 2.2 s/xe; FoRL port tiết kiệm 0.70% nhưng chậm thêm 0.52 s/xe. Cả hai đều là port của chúng tôi, không phải bản gốc của tác giả. | "We ported them to our task; they save fuel but cost the fleet time beyond our limit. They are our ports, not the authors' code." |
| 8 | **Phản biện "tự tạo vấn đề":** đúng là nửa phía đèn của TSI chỉ cần cho đèn đếm xe dừng (W19). Nhưng đó là mặc định của sumo-rl và RESCO (W20), nên vấn đề không phải do chúng tôi tự tạo. | Xem Q1. |
| 9 | **Reward:** reward không dùng ngưỡng (độ trễ) làm tác hại giảm còn một nửa (+0.85 so với +1.70 s/xe), nhưng vẫn cần sửa. | "The reward's threshold accounts for about half; the input's threshold is the main cause." |
| 10 | **Hằng số 10/20/60 và hệ số chia reward 10** là số tròn chọn tay, không tune. Đã thử ÷2, ×2 và reward /1, /100: tác hại và cách sửa giữ nguyên (W19 giai đoạn 3). | "They are standard scale choices; halving, doubling or rescaling them changes nothing." |
| 11 | **Biểu diễn benchmark** (sumo-rl, RESCO) được **cài lại** và huấn luyện bằng **DQN của chúng tôi**, không phải learner gốc (pfrl). Cùng state và reward, khác learner. | "We used the libraries' state and reward definitions with our own learner." |
| 12 | **Thuần mô phỏng.** Mạng tổng hợp (grid4, rand3, spider) cộng một hành lang Salt Lake City với nhu cầu ghi thật. Chưa chạy thử trên đường. | "It's simulation, with the components checked against field data; a road pilot is next." |
| 13 | **Salt Lake City:** khi nâng cấp lên đèn học giàu đầu vào (13 đầu vào), **đội xe không mất lợi ích**, nên không có gì để TSI cứu; TSI ở đó còn kém lịch cũ. Khớp với W19: đèn thấy nhiều hơn thì không bị lỗi. | "On Salt Lake demand the richer light did not break the fleet, consistent with our finding that lights seeing more than stop counts are fine." |
| 14 | **Tài xế IDM:** thiết kế TSI cố định không giữ được khi mọi xe dùng IDM (W9-4, W16). | "Under a different car-following model the frozen design does not carry over unchanged; it needs recalibration." |
| 15 | **Tỷ lệ đội xe:** TSI gốc ở 75% xe là đội: −4.75%, trong giới hạn. Ở 25%: −4.13%, nhưng thời gian xe đội ở sát biên (upper +0.4986), "not robust". TSI-G chưa thử các tỷ lệ khác. | "At 75% fleet share it held; at 25% it was at the margin; for TSI-G that's next." |
| 16 | **Lần xác nhận TSI đầu tiên** (adapter chung cho mọi đèn, C-114): nhiên liệu −4.56% nhưng xe đội chậm thêm +0.85 s/xe (upper +1.27), trượt giới hạn thời gian. Con số −3.85% là của lần xác nhận đăng ký thứ hai (TSI-2, adapter theo từng đèn). | Chỉ nói nếu bị hỏi cụ thể về lịch sử: "The first registered attempt saved more fuel but cost the fleet time; the second, with per-signal calibration, met every limit." |
| 17 | **TSI-G cần biết xe nào dùng SPaT** (qua V2X) và một tham số hiệu chỉnh (CREEP = 3 s). Bộ dự báo phía xe cần 8 episode log của mỗi đèn. | Xem Q3. |
| 18 | **TSI-G trên RL-H** tốt hơn TSI gốc về thời gian xe đội (−0.32 s/xe), nhưng xe người chậm hơn so với TSI 0.57 s/xe; so với không có SPaT thì xe người vẫn không bị chậm (−0.08). | "TSI-G shifts a little time from human cars back to the cooperating cars, compared with TSI; against no SPaT nobody waits longer." |
| 19 | **RESCO wave** (đếm mọi xe): TSI-G cho kết quả **trùng hệt** chỉ dự báo, vì bản sao không đổi số xe trên làn, nên TSI-G không gây hại cho đèn không cần sửa. | "Where the light already sees every car, TSI-G changes nothing, so it is safe to deploy everywhere." |
