# Poster TSI, bản 09/10/2026: vì sao sửa chữ, và kịch bản thuyết trình

Poster in: `research/papers/TSI_two_population/TSI_poster_v4.pdf`; bản sửa được: `TSI_poster_v4.pptx`.
Bản cũ của anh/chị (06/10) vẫn giữ nguyên ở thư mục gốc repo: `Staged Upgrades of Two Learned Populations (1).pptx`.

Tiêu đề **không đổi**, để khớp với tên đã đăng ký cho buổi poster. Phụ đề cũ vẫn đúng: TSI và TSI-G đều là giao diện hai phía khôi phục lợi ích của đội xe khi đèn được nâng cấp.

---

## Phần 0. Vì sao các câu cũ lỗi thời

Poster cũ được viết ngày 06/10, dựa trên kết quả đến W12. Sau đó đã có thêm:
- **W13–W15:** bản TSI sửa đổi;
- **dữ liệu thực địa:** F2–F4, Salt Lake;
- **W16–W18:** thế giới tài xế khớp thực địa;
- **W19:** nguyên nhân là ngưỡng dừng;
- **W20:** các benchmark sumo-rl/RESCO và TSI-G.

Một số câu cũ vì thế đã sai, hoặc không còn là điều quan trọng nhất.

| Câu cũ trên poster | Vì sao lỗi thời | Bằng chứng mới (ledger) |
|---|---|---|
| "The saving holds with HBEFA4 but becomes a 1.76% fuel increase with PHEMlight5" (Limitations) | Chỉ đúng với **thiết kế TSI ban đầu**: dự báo q0.5, (A, B) chỉnh từng đèn. Bản sửa đổi công bố quantile 0.1 và dùng một cài đặt mặc định (1, 0.25) cố định trước; bản này tiết kiệm **dưới cả hai** mô hình nhiên liệu. Dữ liệu thực địa (VED) cho thấy PHEMlight5 mới là mô hình đáng tin hơn, nên điểm này rất quan trọng. | FRESH3 −5.54% / −3.22% (C-19x, W15); W19 AH: −5.57% (HBEFA4), −3.25% (PHEMlight5), C-226; F2: C-198 |
| "the frozen design does not survive IDM drivers" | Vẫn đúng, nhưng chưa đủ. W16–W17 cho thấy với tài xế hiệu chỉnh từ dữ liệu thật (NGSIM), **chính đội xe** chỉ tiết kiệm khoảng 1%. Vì vậy câu đúng là "**phần nhiên liệu đang bị đe dọa nhỏ**", và tác hại chính là **thời gian** của xe hợp tác. | W16 C-209, W17 C-218, W18 C-223 |
| "About three-fifths of the benefit comes back" | Con số 3/5 tính từ −3.85% so với 6.5%, của thiết kế cũ, chỉ dưới HBEFA4. Lợi ích "6.5%" lại phụ thuộc mô hình tài xế Krauss. Câu đúng hơn là: "**sửa được, đạt mọi giới hạn, dưới cả hai mô hình nhiên liệu**". | C-114/C-159, W15, W19 |
| "(A, B) tuned per signal. Calibration costs 52 simulated episodes per signal" | Đã có **một cài đặt mặc định cố định trước** dùng được cho các đèn mới, không cần chỉnh từng đèn. TSI-G còn tổng quát hơn: chỉ một tham số vật lý, hiệu chỉnh trên log toàn xe người. | W9-5, W15 default TG; W20 C-227 |
| "One adapter setting, (A, B) = (1, 0.5)..." | Cài đặt mặc định hiện dùng là (1, 0.25) kèm q0.1 (W15). | W15 |
| "The fleet's inputs need not reveal the problem: ... ten times worse" | Vẫn đúng (định lý), nhưng **không còn là thông điệp chính**. Thông điệp chính giờ là **nguyên nhân**: ngưỡng dừng 0.1 m/s, đã kiểm chứng bằng thí nghiệm nhân quả. | W19 C-226, C-228, C-229 |
| "...though the learned signals are not threshold rules" (Methodology, continued) | W19 cho thấy **chính ngưỡng** (đếm xe dừng) gây ra vấn đề. Cùng công thức huấn luyện nhưng thấy tốc độ hoặc vị trí xe thì không bị hại, và đèn không kéo dài pha xanh. | W19 |
| "For cities and carmakers: ... check that the light still sees cars that slow early, and test single-lane roads first" | Thông điệp chính xác hơn: "**kiểm tra đèn đếm cái gì**". Đếm xe dừng / thời gian chờ thì hỏng; theo tốc độ, vị trí, hoặc dùng cảm biến bản sao người lái thì không. Đây cũng là **mặc định** của sumo-rl và RESCO. | W19, W20 |
| Fig. 3 cũ (forest plot mọi kiểm định TSI) | Quá dày, chữ quá nhỏ để in. Thay bằng hình kết quả chính mới: **ai phải trả giá**, theo đèn đếm cái gì. | — |
| Dòng tác giả "Vu Phan An Nguyen, Zhengping Jay Luo" | Sửa theo yêu cầu: tên anh/chị ở trên, "Mentor: Dr. Jay Zhengping Luo" ở dưới. | — |

**Những gì vẫn đúng và được giữ:**
- Fig. 1 (nâng cấp xóa lợi ích, thế giới Krauss).
- Fig. 2 (vòng kín).
- Fig. 4 (cơ chế: pha xanh dài ra).
- Định lý về hàng đợi theo ngưỡng.
- Kết quả xác nhận −3.85%.
- DC-Ada/FoRL không đạt giới hạn.
- Kết quả chuyển giao (rand3, spider) và độ bền.

---

## Phần 1. Số liệu cần thuộc

| Điều | Số |
|---|---|
| Đội xe tiết kiệm dưới đèn cố định (Krauss, grid4) | 6.5% nhiên liệu |
| TSI, xác nhận đã đăng ký | −3.85% nhiên liệu (95% CI 3.26–4.43), mọi time loss trong giới hạn |
| TSI mặc định trên đèn và đội xe mới | −5.6% (HBEFA4), −3.3% (PHEMlight5) |
| Chỉ công bố dự báo, đèn RL-H (đếm xe dừng) | xe đội trễ thêm **+1.7 s/xe**; pha xanh dài thêm 11% |
| Chỉ công bố dự báo, đèn thấy tốc độ / vị trí | **không hại** (−0.4 s/xe); pha xanh +0.5–2.3% |
| Reward không ngưỡng (đầu vào RL-H) | tác hại giảm còn một nửa (+0.85 s/xe), vẫn cần sửa |
| Đổi hằng số 10/20/60 (÷2, ×2), reward /1, /100 | tác hại và cách sửa giữ nguyên |
| sumo-rl mặc định, chỉ dự báo | **+5.4 s/xe** cho xe đội |
| RESCO IDQN/IPPO, chỉ dự báo | **+2.6 s/xe** |
| RESCO MPLight, chỉ dự báo | **+16.0 s/xe** (nặng nhất) |
| TSI-G trên sumo-rl và RESCO IDQN/IPPO | −0.18 và −0.23 s/xe; nhiên liệu −7.9% và −5.4%; đạt mọi giới hạn (đã đăng ký, α 0.0125) |
| TSI-G trên RESCO MPLight | +16.0 → **+0.51 s/xe** (xóa khoảng 97% tác hại) nhưng **vượt nhẹ giới hạn +0.5**, nên kiểm định đăng ký **không đạt**; nhiên liệu −9.6% |
| Tham số duy nhất của TSI-G | CREEP = 3 s; tổng thời gian dừng bản sao / thực tế = 0.98 |
| Tài xế hiệu chỉnh thực địa (NGSIM) | đội xe chỉ tiết kiệm khoảng 1% |
| Salt Lake City (nhu cầu thật) | đội xe tiết kiệm khoảng 10%; đèn học giàu đầu vào không làm mất |
| Thiết kế thí nghiệm | 5 đèn × 4 đội xe × 20 seed giao thông mới; bootstrap chéo; luật quyết định chốt trước |

---

## Phần 2. Pitch 30 giây (học thuộc)

> Traffic lights and connected cars are both becoming AI, and they are owned and upgraded by different people. We found that when cars use the light's timing to glide instead of stopping, a learned traffic light that only counts stopped cars stops seeing them, and serves them later. So the AI light punishes exactly the cars that cooperate with it. This is the default design in the two most used open-source libraries. We fix it without retraining either AI: we tell the cars a calibrated forecast, and we let the light sense each connected car as the human driver it replaces.

*Nghĩa:* Đèn và xe kết nối đều thành AI, do những bên khác nhau sở hữu và nâng cấp. Khi xe dùng thông tin thời gian đèn để lướt thay vì dừng, đèn học vốn chỉ đếm xe dừng sẽ không thấy những xe đó và phục vụ chúng muộn hơn. Tức là đèn AI phạt đúng những xe hợp tác với nó. Đây là thiết kế mặc định của hai thư viện mã nguồn mở phổ biến nhất. Chúng tôi sửa mà không huấn luyện lại AI nào: báo cho xe một dự báo đã hiệu chỉnh, và cho đèn cảm nhận mỗi xe kết nối như chiếc xe người lái mà nó thay thế.

---

## Phần 3. Đi qua poster trong 2 phút (học thuộc; [ngoặc vuông] = chỉ tay vào đâu)

**1. Bối cảnh, khoảng 20 s** [chỉ Fig. 1]
> Every stop at a red light wastes fuel. If the light broadcasts when it will turn green, connected cars can ease off early and glide through. In our simulation an AI eco-driving fleet saves six and a half percent fuel this way under fixed-time lights. But when the lights themselves become AI-controlled, that saving disappears.

*Nghĩa:* Mỗi lần dừng đèn đỏ là tốn nhiên liệu. Nếu đèn phát khi nào sẽ xanh, xe kết nối có thể nhả ga sớm và lướt qua. Trong mô phỏng, đội xe AI tiết kiệm 6.5% nhiên liệu dưới đèn cố định. Nhưng khi đèn thành AI, khoản tiết kiệm đó biến mất.

**2. Nguyên nhân, khoảng 25 s** [chỉ Fig. 2]
> Here is why. Most learned lights count a car as waiting only once it has stopped, below 0.1 meters per second. A car that glides never counts. So the light thinks that approach is empty, holds the other green longer, and the gliding cars arrive at a red light anyway. The forecast defeats itself.

*Nghĩa:* Lý do: hầu hết đèn học chỉ coi một xe là đang chờ khi nó đã dừng, dưới 0.1 m/s. Xe lướt không bao giờ được đếm. Đèn tưởng hướng đó trống, giữ pha xanh kia lâu hơn, và xe lướt vẫn đến lúc đèn đỏ. Dự báo tự phá chính nó.

**3. Cách sửa, khoảng 25 s** [chỉ cột giữa, phần Fleet side / Light side / TSI-G]
> We keep both AIs frozen and change only two interfaces. On the car side, a forecast calibrated on the deployed light's own logs. On the light side, the light senses each connected car as the human it replaces: where that car would be, and whether it would be stopped, if a person were driving. Then every count the light uses, queues, waiting times, pressure, is computed on those twins. It has one parameter, calibrated on human-only data.

*Nghĩa:* Giữ nguyên cả hai AI, chỉ đổi hai giao diện. Phía xe: một dự báo hiệu chỉnh trên log của chính đèn đang chạy. Phía đèn: đèn cảm nhận mỗi xe kết nối như chiếc xe người lái mà nó thay thế, tức xe đó sẽ ở đâu và có đang dừng không nếu người lái. Mọi đại lượng đèn dùng (hàng chờ, thời gian chờ, pressure) được tính trên các bản sao đó. Chỉ một tham số, hiệu chỉnh trên dữ liệu toàn xe người.

**4. Kết quả, khoảng 35 s** [chỉ Fig. 3]
> This figure is the main result. Orange is the forecast alone; blue is with our repair. Every signal that counts only stopped cars makes the cooperating cars wait longer: almost two seconds per vehicle for our signal, more than five for the sumo-rl default, sixteen for RESCO's MPLight. With the repair they come back to about zero without retraining; all but MPLight are within our limits, and MPLight misses by a hair. And the bottom half shows the control: lights that see speed or position were never harmed. We also changed every constant and the reward; the pattern did not move.

*Nghĩa:* Đây là kết quả chính. Màu cam là chỉ công bố dự báo, màu xanh là có bản sửa. Mọi đèn chỉ đếm xe dừng đều làm xe hợp tác chờ lâu hơn: gần 2 s/xe với đèn của chúng tôi, hơn 5 s với mặc định của sumo-rl, 16 s với MPLight của RESCO. Có bản sửa thì tất cả về gần 0 mà không cần huấn luyện lại. Trừ MPLight, tất cả nằm trong giới hạn; MPLight chỉ vượt rất nhẹ. Nửa dưới là đối chứng: đèn thấy tốc độ hoặc vị trí không bao giờ bị hại. Chúng tôi cũng đổi mọi hằng số và reward; mẫu hình không đổi.

**5. Thực địa và kết luận, khoảng 15 s** [chỉ cột phải, "Field data" và "Conclusions"]
> Field data keep us honest: with drivers calibrated on real trajectories the fuel at stake is small, about one percent, so the main harm is fairness, the time penalty on cooperating cars. The lesson for cities is simple: before deploying a learned light where cars use SPaT, check what it counts.

*Nghĩa:* Dữ liệu thực địa giữ chúng tôi trung thực: với tài xế hiệu chỉnh từ quỹ đạo thật, phần nhiên liệu bị đe dọa nhỏ, khoảng 1%. Vì vậy tác hại chính là công bằng: xe hợp tác bị phạt thời gian. Bài học cho thành phố: trước khi triển khai đèn học ở nơi xe dùng SPaT, hãy kiểm tra đèn đếm cái gì.

---

## Phần 4. Câu hỏi dễ gặp (trả lời ngắn, tiếng Anh)

**Q1. Didn't you create the problem by choosing a halting-count signal?**
> That was our worry too, so we tested it. Stop-based counts are the default in sumo-rl and in RESCO's IDQN, IPPO and MPLight. We retrained signals by the same recipe with only the input changed: with speed or position inputs, no harm and no repair needed. With the library defaults the harm is larger than with ours: 2.6 to 16 seconds per vehicle.

*(Đây đúng là phản biện anh/chị đã nêu; W19 và W20 trả lời nó.)*

**Q2. What exactly is the "human twin"?**
> For each connected car, we compute where a human driver would be: driving at its free speed from where it entered the lane, braking, following the car ahead, stopping at the back of the queue, and starting after the car in front moves. The light's counts use that position and speed instead of the glider's.

**Q3. What information does TSI-G need?**
> Which cars follow SPaT. They already talk to the infrastructure by V2X. Plus one site parameter, how long a human rolls before fully stopping, calibrated on ordinary human-only logs. Here it is 3 seconds, and the twins reproduce human stopped time within 2%.

**Q4. Why not just retrain the signal?**
> The lights and the cars are owned by different parties and upgraded on different schedules. Retraining needs both sides together. And if you can redesign the light, our results say: give it speed or position inputs.

**Q5. How much fuel is really at stake?**
> Less than simulators suggest. Measured fuel data favour the PHEMlight5 model, and real drivers brake much earlier than SUMO's default driver. With drivers calibrated on real data the fleet saves about one percent; on recorded Salt Lake City demand, about ten. So we put the time and fairness harm first.

**Q6. How do you know the results are not luck?**
> Every decision rule was registered before the confirmation run. Five independently trained signals, four fleets, twenty fresh traffic seeds, and a crossed bootstrap over all three. Self-checks recompute every input independently.

**Q7. Why two fuel models?**
> HBEFA4 and PHEMlight5 can disagree on gliding. We report both, and our default repair saves fuel under both.

**Q8. The constants 10, 20, 60 look arbitrary.**
> They are hand-picked scales, and we tested that: halving or doubling them, or rescaling the reward, leaves both the harm and the repair in place.

**Q9. Is it only simulation?**
> Yes, mostly synthetic grids plus one corridor with recorded demand. The fleet and signal behaviours were checked against field data, but not deployed. That is the main limitation.

**Q10. What happens with more or fewer connected cars?**
> For the original repair we tested fleet shares of 25 and 75 percent: it stayed within the limits, only at the margin at 25 percent. For TSI-G and the library defaults that is the next experiment.

*(Số liệu: share 75% −4.75%, trong giới hạn; share 25% −4.13%, agent time upper +0.4986, sát biên, "not robust"; paper tab. scope, C-121/C-128.)*

**Q11. What is the theorem for?**
> It predicted the result before we ran it: in a threshold-queue model, a signal that counts slow cars as waiting needs no light-side change, and each one-sided fix fails alone.

**Q12b. Does TSI-G always work?**
> Not always within our strict limit. On RESCO's MPLight state the harm drops from sixteen seconds per vehicle to half a second, which is just over our 0.5 limit, so we report it as not shown.

**Q12. What is new compared with prior work?**
> Earlier work fixes one side: better forecasts, or smarter cars, or retraining. We show that the two AIs interact through what the light counts, and we repair that interaction without retraining either one.

---

## Phần 5. Mẹo trình bày
- Mở bằng pitch 30 giây, rồi hỏi người nghe muốn nghe chi tiết hay không.
- Luôn **chỉ vào Fig. 3** khi nói kết quả: cam là chỉ dự báo, xanh là có sửa, nửa dưới là đối chứng.
- Nếu ai hỏi "con số 6.5% có thật không": nói thẳng chuyện dữ liệu thực địa (Q5). Trung thực sẽ tạo uy tín.
- Nếu không biết: "That's a good question; we haven't tested it yet, it's on our list."
