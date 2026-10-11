# Báo cáo chiều 04/10/2026 (cập nhật liên tục)

Đích giữ nguyên: một paper phương pháp cho nâng cấp so le giữa hai quần thể học, đèn và đội xe. Mốc đang chặn là **M1: có một fleet học đáng dùng**. Không dùng subagent. Mọi thay đổi đều có protocol trước khi chạy (\`research/city_sim/PROTOCOL_CITY_SPAT_PILOT_20261004.md\`, Amendment R1–R5).

## 1. Đã làm và đã biết

| Việc | Kết quả | Ledger |
|---|---|---|
| Đính chính theo audit (A–F, SPaT 1–7) | Nhãn S-2 kiểm lại: 11/12 fleet cũ bị σ dominate thật, R4v6_t1 chỉ là chưa tách được. R5h vượt họ σ nhờ xăng. Các claim quá mạnh đã thu hẹp. | C-37 |
| SPaT theo movement, kiểm trên trace | Dưới FT khớp 100 % sau quy ước +1 s. Trace-check có assertion, và được thử làm hỏng có chủ ý để chắc nó fail được. | C-38, C-38b |
| Đối chứng dưới FT | σ\* = 0.3 (quy tắc chốt trước). ctrl ≡ always-SUMO. | — |
| Reward B (bài Jayawardana–Wu, Eq. 9–10) | Port theo đơn vị L/s. Calibration: không suy biến. R4 không bao giờ kích hoạt, nên xăng chỉ vào reward qua ngưỡng δ. | R3 |
| Pilot B (PPO, 12 run) | 4 run pilot đang chạy theo đăng ký. 8 run xác nhận tạm dừng, chỉ chạy tiếp nếu pilot qua gate. | — |
| **D1, reward có xếp đúng hành vi không** | B nhìn chung đúng hướng ở chênh lệch lớn, nhưng **không mã hoá ràng buộc TL**: xếp một clone chậm +21.6 s/veh cao hơn hẳn always-SUMO, vốn khả thi. **PPO pilot thua always-SUMO rất xa ngay trên traffic train** (TL +245…+314). | C-39, C-42 |
| **D2, learner có học được hành vi tốt đã biết không** | GLOSA heuristic là positive control khả thi (xăng −7.9 %, TL −1.1). Controller viết tay trong lớp action: xăng −6.7 %, TL ≈ 0, nhưng hại xe người, nên lớp action biểu diễn được hành vi gần tốt. Clone GLOSA: xăng −5 % nhưng TL +21.6. | C-40, C-42 |
| **Bug eval tìm được nhờ kiểm identity** | Ở chế độ eval, fleet PPO không release khi xe rời vùng. Đã sửa (training không đổi). Các hàng bị nhiễm đã lưu \`legacy/\` và chạy lại. | C-41 |
| **R7a, GLOSA trên tài xế nền σ\* (15:00)** | P7-1 và P7-2 **FAIL** theo tiêu chí đăng ký. Về ước lượng điểm, phần lớn khoảng cách TL tới σ\* đến từ tài xế nền: +1.84 → −0.10 trên SELECT, +2.83 → +0.45 trên 420–429. Phần còn lại là vài seed bị kẹt, có 2–4 teleport do chính fleet gây ra. | C-44 |
| **Phát hiện: mọi fleet ra lệnh tốc độ đều tự gây deadlock đổi làn (15:09)** | Always-SUMO và σ đều 0 teleport. Mọi fleet có ra lệnh (GLOSA, IC-GLOSA, PPO, BC, R5h) đều có 2–17 teleport mỗi run. Các sự kiện đã soi đều cùng một kiểu: một xe agent đứng ở cuối một làn không đi tiếp được, đứng 300 s rồi teleport. Nguyên nhân là `setSpeed` ghi đè việc SUMO tự chỉnh tốc độ để đổi làn. **Mọi kết quả fleet học trước đây đều bị lẫn chi phí này** (gọi tên là confound; không vì thế mà đổi nhãn các kết quả fail). **Thu hẹp (C-50):** đây là bằng chứng trên các trace và panel đã soi. Chưa có factorial cùng checkpoint × interface cũ/mới, nên **không** quy toàn bộ thất bại PPO/BC/R5h cho deadlock; reward và khả năng học vẫn có thể là vấn đề. | C-45, C-50 |
| **R8, lane-aware release (15:11)** | P8-1 đúng: teleport về 0 trên 5 seed dev. **P8-2 đúng trên traffic MỚI 430–449 (20 seed): GLOSA-L∘σ\* so với σ\*: xăng −5.0 %, TL agent −0.7, TL xe người −0.4, tốt hơn trên cả ba trục; so với always-SUMO: xăng −7.1 %, TL −3.3, 0 teleport.** P8-3 (xăng ≤ −6 %) FAIL. Đây là luật cố định, chưa phải M1. Nó là baseline mạnh cùng thông tin mà fleet học phải vượt. | C-46 |
| **Kiểm credit R10 (theo audit, 16:02)** | (A) Chi phí bị bỏ khi cắt episode chỉ 0.09–0.17 %, ghi sổ khớp chính xác. (B) Discount tính **theo quyết định**: 97.9 % khoảng cách giữa các quyết định là 1 s, nhưng return theo quyết định lớn hơn return theo giây khoảng 12 % (trung vị). Đây là objective theo lần can thiệp, đã khai báo. (C) Tính theo chuyến, chi phí train giảm 3–4 % trên cả 6 seed trong khi số quyết định không đổi. Đây chưa phải endpoint. | C-51 |
| **R6, policy search 3 tham số GLOSA (14:50)** | **Gate FAIL.** Search seed 1 trả về đúng GLOSA chưa chỉnh: trong lớp này, GLOSA heuristic gần như là tối ưu cục bộ trên traffic train. So với always-SUMO: xăng −7.8 %, TL agent −0.7, nhưng cận trên TL xe người +1.02 vượt margin 0.5 (ước lượng điểm chỉ +0.12, nên lỗi nằm ở độ rộng khoảng tin với 5 seed). So với σ\*: TL agent +1.8, FAIL. Theo đăng ký, xác nhận không chấm. | C-43 |

## 2. Đang chạy, mỗi bản chỉ đổi một thứ, có dự đoán ghi trước

| Run | Thay đổi | Trạng thái |
|---|---|---|
| **v9** (R4) | PPO học phần dư δ trên controller viết tay (δ = 0 ≡ controller, kiểm bit-identical); reward vật lý theo nhóm pha, chống bò | **Pilot gate FAIL (15:28):** TL xe người khoảng +2.9, nhưng nền IC-GLOSA đã mang sẵn mức đó (không release, nên deadlock). So với nền, phần dư **có học**: xăng −1.9 % và −2.9 % (cận trên < 0), TL không tệ hơn. Xác nhận không chấm. C-47. |
| **v10** (R5) | v9 + **credit dày theo từng xe**: delay và xăng của chính xe, cộng delay của xe phía sau | **Pilot gate FAIL (15:38):** TL xe người +3.5, vẫn do nền. So với nền: xăng −1.0…−1.3 % nhưng TL agent +1.55, tức là kém v9. R10 cũng dùng cost dày này, nên đây là tín hiệu cảnh báo cho R10. C-48. |
| Pilot B | như đăng ký | xong khoảng 15:20 |
| **R9** (đăng ký 15:12) | **Fleet học phải vượt GLOSA-L∘σ\*.** Search 4 tham số; tham số mới d_lc giới hạn lane-aware release vào d_lc mét cuối làn, để lấy lại phần xăng bị mất. Gate = (a) VÀ (d″) so với GLOSA-L∘σ\*: xăng superiority, TL agent/người NI. Xác nhận trên traffic MỚI 450–469. Luật M1: (a), (b), (d″) trên bản xác nhận. Identity PASS. | **Pilot GATE PASS (16:00).** P9-1 đúng trên 5/5 seed (d_lc ≈ 12–22 m). Trên SELECT, so với GLOSA-L∘σ\*: xăng **−3.6 %**, TL agent −0.64, TL xe người +0.08 (cận trên +0.19), 0 teleport. So với σ\*: xăng −8.2 %, TL −1.07. Đang chấm xác nhận trên 450–469. C-52. |
| **R7b** (search trên nền σ\*, chưa lane-aware) | **Pilot gate FAIL (15:42).** Search có dịch θ (cả 5 seed đều nâng tốc độ sàn chống bò lên 1.4–2.9 m/s), nhưng trên SELECT không khác GLOSA∘σ\* (xăng −0.03 %). Phương sai do deadlock vẫn còn. Xác nhận không chấm. C-49. | xong |
| **R7** (đăng ký 14:55) | **Một thay đổi: tài xế nền.** Mọi fleet GLOSA trước đây, khi release, chạy SUMO với σ 0.5; σ\* chạy 0.3 suốt chuyến. R7 đặt σ\* làm tài xế nền cho xe agent và giữ nguyên mọi thứ khác. R7a: GLOSA∘σ\*, luật cố định, là baseline "cùng thông tin" trên nền mạnh. R7b: search lại θ trên nền này, J tính so với σ\*. Dự đoán: P7-1, GLOSA∘σ\* qua (b) so với σ\*; P7-3, search lại trả về ≈ θ0. Identity K7-1…3 PASS bit-identical. | R7a eval và R7b 5 seed đang chạy |

Eval tự chạy khi train xong. Gate: một seed pilot đạt (a) so với always-SUMO. Sau đó có (b) so với σ\*, (d) so với controller nền, và xác nhận trên seed và traffic mới.

## 3. M1 — trạng thái cuối chiều (16:06)

**M1 đạt theo luật đã đăng ký (R9, C-54).** Fleet GLOSA-LD∘σ\*: 4 tham số policy được fit bằng search không đạo hàm trên traffic TRAIN. Xác nhận trên traffic MỚI 450–469, 4 seed search × 20 traffic:

| So với | Xăng agent | TL agent | TL xe người | Teleport |
|---|---|---|---|---|
| always-SUMO | −9.68 % | −3.48 | −0.49 | 0 vs 0 |
| σ\* (họ không học mạnh nhất) | −7.58 % | −0.78 | −0.36 | 0 vs 0 |
| luật GLOSA-L∘σ\* (cùng nền, cùng SPaT, cùng interface) | **−2.80 %** | −0.18 | −0.01 | 0 vs 0 |

Mọi cận 95 % đều nằm phía có lợi hoặc trong margin. Per-seed (d″): 4/4. Provenance khớp hash đã freeze; 0 unfinished.

**Giới hạn phải nói rõ (C-54, C-55):**
- Đây là policy được fit, không phải RL hay MARL, không phải thuật toán eco-driving mới. Chưa so với các eco-controller đã công bố. Chỉ chạy dưới đèn FT; đèn học/actuated thuộc M2.
- So với GLOSA∘σ\* (không lane release), xăng **ngang bằng** (+0.16 %), nhưng TL tốt hơn 0.77 và 0 teleport (GLOSA∘σ\*: 0.40). Phần học được chủ yếu là **chỗ nhả quyền lái** (d_lc ≈ 15 m), không phải một hành vi eco mới.
- Ablation SPaT: không có SPaT thì policy không bao giờ ra lệnh, tức là trở thành σ\*. Như vậy (b) chính là ablation SPaT ở cấp lớp policy (xăng −7.6 %). Thông tin và biểu diễn chưa được tách riêng.

**Fleet RL (PPO):** B (C-53), v9 (C-47) và v10 (C-48) fail gate. **R10 (PPO học phần dư trên luật R8) cũng đạt luật M1 trên bản xác nhận (16:28, C-57).** Gộp 4 seed × 20 traffic mới:

| R10 so với | Xăng | TL agent | TL xe người |
|---|---|---|---|
| always-SUMO | −8.66 % | −3.33 | −0.47 |
| σ\* | −6.54 % | −0.64 | −0.33 |
| luật GLOSA-L∘σ\* | **−1.70 %** | −0.04 | +0.02 |

Per-seed (d″): 4/4. 0 teleport, provenance khớp. So với GLOSA∘σ\* (không lane release), R10 **kém hơn về xăng** (+1.3 %), nhưng TL tốt hơn và không có teleport. Tức là PPO thêm được ~1.7 % trên luật, ít hơn R9 (−2.8 %), vì R10 không học chỗ nhả quyền lái. Objective của R10 tính theo lần can thiệp (C-51).

## 4. M2 — đã mở (16:32, theo bước 4 của audit R8–R10)

Protocol `PROTOCOL_CITY_M2_COMPAT_20261004.md`, đăng ký trước khi chạy, chỉ có eval:
- **Đèn:** FT → đèn học RL-H (4 seed, frozen).
- **Fleet:** always-SUMO, σ\*, R9, R10, tất cả frozen.
- **Hai arm SPaT dưới đèn học:** "naive" (dùng nguyên SPaT suy từ chương trình tĩnh, vốn ngoài phạm vi dưới đèn học) và "labelled" (đèn học khai báo không có SPaT, fleet tự nhả quyền lái).
- **Traffic:** mới 470–489.

Check PASS. Phát hiện từ check (C-58):
- Dưới RL-H, 29 % số lần gọi SPaT được implementation gắn `valid` dù đã ra ngoài phạm vi bảo đảm của nó. (Đính chính C-60: đây là số lần gọi, **không phải** tỷ lệ forecast đã đo là sai.)
- Smoke một seed: fleet R9 ở arm naive bị hại, xăng +7.5 % và TL +1.6 so với σ\*. Arm labelled thì trùng từng bit với σ\*, tức là mất lợi ích nhưng không bị hại.
- City TL ~21 s dưới RL-H so với ~53 s dưới FT, nên đây là một bản nâng cấp đèn rất mạnh.

**Kết quả panel (16:41, C-59), traffic mới 470–489:**

| | R9 (F0a) | R10 (F0b) |
|---|---|---|
| Lợi ích của fleet so với σ\* dưới **FT** (xăng) | −7.5 % | −6.5 % |
| Dưới **RL-H, labelled** (đèn không phát SPaT) | **0** (trùng σ\*): mất lợi ích, không hại | **0**: như R9 |
| Dưới **RL-H, naive** (SPaT suy từ chương trình, sai) | **+7.4 % xăng, +1.7 s TL**: bị hại | **+6.5 %, +1.6 s**: bị hại |
| DiD xăng (naive / labelled) | +15.0 / +7.5 điểm | +13.0 / +6.5 điểm |

- Nâng cấp đèn (M2-A): city TL −33.7 s/xe, city fuel −19.5 %.
- Tính tuyệt đối, xe agent dưới RL-H vẫn tốt hơn hẳn so với dưới FT ở mọi arm. Thứ bị mất là **lợi ích riêng của fleet** so với σ\* dưới cùng đèn mới.
- Dự đoán: P-M2-1 đúng, P-M2-2 đúng, P-M2-3 NOT SUPPORTED (hại lớn hơn dự đoán; 30–43 % số lần gọi được gắn `valid` ngoài phạm vi bảo đảm, chứ không chỉ trong pha vàng; đây là số lần gọi, không phải sai số forecast đã đo; C-60).

**Bài toán cho M3 đã rõ:** đèn học phải phát hoặc cam kết một phần kế hoạch, để fleet cũ giữ lợi ích, với chi phí đo được cho chính đèn.

## 5. M3 — pilot DEV (19:32, C-64…C-68)

Protocol M3 + A1 + A1b gồm 10 arm E (E0-queue, E0-physical, uniform, ETA, active, receiver × λ{1,4}) trên 2 seed đèn, cùng các đối chứng F-q, D, W-c, B-ETA và P-cyc. Self-check S1–S14 đều PASS. 127 job DEV.

**Kết quả DEV: không có cấu hình nào khả thi. Không arm E nào làm xăng agent tốt hơn hệ tham chiếu R** (RL-H không phát SPaT, fleet chạy như σ\*).
- E-receiver λ1: xăng **+7.6 %**, city TL +3.0. E0-physical: +3.7 %, city TL +4.1.
- Đối chứng gần nhất là F-q0.1: xăng −0.5 % (không có ý nghĩa thống kê), nhưng TL agent +1.1, nên không khả thi.
- Các đèn có penalty làm forecast rất chính xác (MAE ~1 s, so với ~5 s của E0) bằng cách chuyển pha dày hơn. City TL vì thế tăng 3–7 s, mà fleet R10 đóng băng nhận SPaT chính xác dưới pha xanh ngắn vẫn bị hại.
- Hai đèn fine-tune kẹt cứng khi chạy với xe σ\* ở 2–3/15 traffic, trong khi lúc train có fleet thì không.

**Kết luận pilot:** M3 chưa đạt. Trong setting này, các cơ chế phía đèn (giữ forecast, cam kết, chu kỳ dự đoán được) tốn của đèn nhiều hơn phần chúng trả lại cho fleet. Fallback "đèn không phát SPaT" vẫn chưa bị vượt. Việc có chạy confirmation hay không đang chờ người dùng quyết.

## 6. Kiểm lỗi và F1 (20:07, C-69…C-72)

**Đính chính (C-69, C-70):**
- Rút lại lời giải thích "pha ngắn làm fleet hỏng": P-cyc là phản ví dụ.
- "Đóng góp của fleet" và "chi phí đèn" ở các arm E là hiệu ứng chung của cả hệ, không phải đóng góp riêng.
- Câu về quyền thông tin là sai.
- M3 dừng sau DEV, chưa chạy confirmation.
- Các số đo thô của mọi thí nghiệm hôm nay vẫn đáng tin; xem bảng tác động ở C-70.

**Hai check (C-71):**
- Ở nhánh đèn đang xanh, ttg của forecast **sớm 1 s ở 100 % điểm**. Nghi vấn ban đầu là ttr lệch, nhưng ttr lại đúng.
- Sự kiện oracle khớp lịch replay ở 100 % điểm.

**D-dir (C-72):** fleet đóng băng cực kỳ nhạy với sai số ttg.
- Ttg chính xác cho xăng −6.6 %. Lệch sớm 1 s còn −4.5 %, sớm 4 s còn −1.4 %, muộn 4 s thì TL agent +4.3, muộn 8 s thì xăng +9.3 %.
- Forecast thực nghiệm (MAE 3–8 s, bias −4.6 s, cộng lỗi −1 s) rơi đúng vào vùng mất gần hết lợi ích.

**F1:** protocol đã đăng ký, check PASS. Chuỗi tự động đang chạy: chọn provider đã sửa trên DEV → train F1 và F1-scratch (200 episode) → eval DEV → gate (phải thắng σ\*).

## 7. Tối 04/10 (20:18–21:20, C-73…C-81): M3′, F1, M4

**M3 (phía đèn), mọi cơ chế đều trượt ở DEV:**
- **A2 shadow (C-75):** đo sạch chi phí phía đèn, đèn nhận đúng input như lúc triển khai. Vụ kẹt cứng của E0-physical là do input (0 / 60 khi chạy shadow).
- **M3′ RPC (C-79):** đèn cam kết đúng thời điểm chuyển pha mà chính nó dự đoán, chỉ khi có xe fleet đang chờ đèn đỏ.
  - 0 vi phạm trên 247 498 cam kết.
  - Xăng agent **+9.40 %** so với R. City TL +5.66. Chi phí sạch phía đèn +6.17.
  - Kém cả W-c5 (+3.60 %), kém cả bản trigger ngẫu nhiên (+4.53 %).
  - Tier 1 FAIL, tier 2 không có lợi thế. **Dừng ở DEV.**
- Giả thuyết cơ chế (chưa kiểm vì sidecar không ghi hành động bị override): mỗi cam kết giữ xanh ít nhất 5 s, nên cam kết đúng lúc RL-H muốn chuyển sẽ trễ ít nhất 5 s.

**F1 (fleet thích nghi), C-78 và C-79:**
- F1 fine-tune từ R10: **FAIL** (+0.04 %).
- **F1-scratch** (train từ đầu dưới RL-H với forecast đã sửa, q 0.1): **qua mọi tiêu chí DEV**. Xăng −3.06 % [−3.60, −2.46], agent TL +0.13 (up +0.30), human −0.76, city −0.33, 0 teleport.
- Rule trần (residual 0) dưới cùng điều kiện: +3.28 %. Vậy việc học tạo ra khoảng 6.3 điểm.
- **F1-A1** đã đăng ký (chọn arm sau DEV, khai rõ): confirmation trên 5 đèn mới t4–t8 × traffic mới 530–549, crossed. KA-1…4 PASS. Đang train, report khoảng 21:52.

**M4 (mạng thứ hai spider: netgenerate, 18 đèn, 6 đèn có 3 pha xanh):**
- **Stage 1 (C-76):** đèn học RLK thắng FT −57 s/veh (2 seed). PASS.
- **Stage 2a (C-77):** rule GLOSA-L∘σ\* tiết kiệm −9.2 % xăng so với σ\*.
  - **Đính chính (C-81):** trên traffic mới, ràng buộc TL so với σ\* trượt sát ngưỡng (agent up +0.55, human up +0.52). Trên DEV nó đạt.
- **Stage 2b (C-80):** search R9 KHÔNG thắng rule (+0.40 % xăng). Pilot FAIL. M1-spider: NOT MET.
- **Stage 3 (C-81): M2 lặp lại trên spider.**
  - Nâng cấp đèn: −58.9 s/veh, −26.6 % xăng.
  - Labelled: trùng hệt σ\*, mất trọn lợi ích, không hại.
  - Naive: **bị hại**, xăng +7.16 %, agent TL +2.71, human TL +0.57 (up +0.82).
- **Stage 4** (đưa "phương pháp M3 thắng" sang spider) phụ thuộc F1-A1. Trên spider chưa có forecast cho đèn 3 pha xanh, nên phải đăng ký mô hình mới nếu F1-A1 được xác nhận.

**Cập nhật 21:40 (C-82…C-84):**
- **M4 stage 4a (C-82):** đèn spider giữ cam kết W = 5 với rule fleet đóng băng làm xăng agent **+6.68 %** so với fallback không SPaT (city TL +10.3). Âm tính được lặp lại trên mạng thứ hai.
  - Chi phí sạch phía đèn là +6.61 %. Fleet hoàn toàn không được lợi (+0.06 % [−0.25, +0.39]).
  - Vì vậy lý do "fleet được lợi nhưng không bù chi phí đèn" KHÔNG được xác lập trên spider: toàn bộ thiệt hại là chi phí của đèn.
- **Audit (C-83):** NetInfo của E4 chỉ thấy 2 trong 3 pha xanh ở 6 đèn spider. Chỉ ảnh hưởng các cột mô tả "green", không ảnh hưởng endpoint nào.
- **Lỗi đã chứng minh (C-84):** provider "đã sửa" vẫn sớm 1 s ở một nhánh (đang yellow, link thuộc pha xanh sau pha kế tiếp), 100 % quan sát. Check KF-0/KA-2 không bao nhánh này.
  - F1 DEV và F1-A1 dùng cùng provider ở train và eval, nên so sánh vẫn nhất quán, nhưng phải ghi rõ giới hạn này.
  - Không đổi provider giữa chừng của F1-A1.
  - Provider đa pha xanh mới cho spider (forecast-K) sửa mọi nhánh, và check của nó bao mọi nhánh, kể cả đối chứng âm.
- **Đang chạy:** F1-A1 eval (report khoảng 21:55); M3-NC panel (khoảng 22:05). 4b đã chuẩn bị xong, chỉ chạy nếu F1-A1 CONFIRMED.

## 8. Kết quả cuối wake 2 (22:00): M3 và M4 đã có kết quả đăng ký

- **F1-A1 (C-85): NOT CONFIRMED.**
  - Xăng −2.61 % lặp lại trên 5 đèn mới × 4 fleet × traffic mới.
  - Nhưng agent TL +0.34 (upper **+0.55**), vượt biên +0.5. Gate không nới.
- **M3-NC (C-86): âm tính phía đèn ĐÃ XÁC NHẬN, có lý do.**
  - WC5 +2.98 %, RPC +9.26 %. Cả 20/20 ô đều dương.
  - Message chính xác giúp fleet (−2.4 % / −1.2 %), nhưng chi phí giữ đèn lớn hơn (+5.6 % / +10.6 %).
- **M3: KHÔNG ĐẠT, dưới dạng âm tính đã xác nhận.** Không có "phương pháp thắng".
- **M4: xong trên spider.**
  - Nâng cấp đèn hiệu quả.
  - M2 lặp lại.
  - Âm tính M3 lặp lại.
  - R9 không lặp lại.
  - 4b không chạy, vì điều kiện F1-A1 không đạt.
