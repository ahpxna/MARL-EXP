# Báo cáo đêm 04/10/2026 (cập nhật liên tục; bản đầu 05:57 EDT)

Báo thức đặt mỗi giờ, đến 11:00. Không dùng subagent vì bạn chưa nói "fetch". Mọi thí nghiệm đều có protocol viết trước khi chạy, có smoke, và chạy qua một spool tuần tự (1 thread / process).

## 1. Kết quả chính (theo thứ tự quan trọng)

| # | Kết quả | Ledger |
|---|---|---|
| 1 | **Chưa có đội xe học nào có lợi so với mô hình lái mặc định của SUMO.** Trên 65/65 run cũ, đội xe RL tệ hơn khi tự lái các xe đó (time, fuel, city), kể cả dưới đèn được train. Screen B6-1 (reward v2 và v3 × 2 seed): cả 4 FAIL; v2 tệ nhất (+62…+80 % fuel). | C-17, C-21 |
| 2 | **Hai lỗi đặc tả reward, theo hai chiều ngược nhau.** v1 phạt đứng yên theo tốc độ LỆNH: xe né bằng cách ra lệnh tăng tốc (99.9 %). v2 phạt đứng yên THỰC mà không phạt bò: xe bò ngay trên 0.1 m/s ở 28–32 % thời gian và chiếm vùng tiếp cận lâu gấp đôi. v3 (delay + fuel vật lý) không bò, nhưng vẫn thua; nguyên nhân chưa rõ. | C-13, C-21 |
| 3 | **Nâng cấp đèn, xe đóng băng (chiều A-L):** cổng phản ứng phía xe giúp rõ; clip τ không giúp (trong panel đã thử). Guard green+oos biến nâng cấp đèn thành có lợi so với ACT ở 16/16 ô, cả trên VALIDATION. **Nhưng always-SUMO (tắt đội xe) vẫn tốt hơn mọi biến thể có guard** (+1.24 [0.67, 1.95] s/veh). | C-14, C-16, C-18 |
| 4 | **Provenance:** mô phỏng city không tất định giữa các process; jitter của một run lên tới 1.45 s/veh. Đã sửa: PYTHONHASHSEED=0 bắt buộc; OMP=1 vẫn bit-identical. | C-11 |
| 5 | **Lỗi hot-swap:** `setProgram` không giữ pha. Đã thay bằng chuyển giao ở ranh giới pha (16/16 đèn đúng pha). | C-18 |
| 6 | **Co-training (B3):** cả 4 dự đoán âm. | C-15 |
| 7 | **Paper E3:** E12 chính xác ⇔ coverage (0 ngoại lệ trên 532 480 bước) cùng Lean E12-a (smoke gate PASS, 10 định lý). E14 NOT SUPPORTED (FT-mix / PCT vẫn là tham chiếu). Đã có claim table mới với câu chữ được phép. | L-330, L-331, L-332 |
| 8 | **Sửa manuscript:** FUNCTIONAL g ≥ 0 (khớp Lean); Paper C: limitation odd đã cập nhật theo `recourse_one_odd_all` (đã qua gate). Cả hai biên dịch lại OK. | — |

## 1b. Cập nhật 06:24

- **B6-N (policy class chứa baseline): N-1 FAIL.** Class có hành động "nhả quyền cho SUMO" vẫn thua baseline (TL +22…+29 s/veh) và chỉ nhả 5–19 % số lần. Recipe DQN không tìm ra baseline dù nó nằm trong class, nên vấn đề là tối ưu hoá / dữ liệu, không phải tập hành động.
- **Lỗi thật mới tìm thấy (C-22).** Khi xe đang teleport, libsumo trả sentinel −1073741824 cho speed / fuel / acceleration mà không ném lỗi. Reward v3 đọc phải và tạo reward dương khổng lồ.
  - Đã tái hiện chính xác (+11.858 trùng log).
  - Arm residual của 039 và R4 của B6-R bị loại; v3 và release không bị nhiễm.
  - Trainer v6 làm sạch giá trị đọc: bắt đúng 33/33 sentinel trên episode lỗi.
  - Đã xếp chạy lại: 040b (residual) và 040c (R4, cùng R1 nếu bị nhiễm).
- **Chẩn đoán mới đã xếp hàng: B6-I (040d).** Behavior cloning mô hình lái của SUMO vào tập hành động rời rạc, để tách "class không biểu diễn được" khỏi "RL không tìm ra".

- **Paper E3:** đã có 3 hình (E7 các arm kèm byte; E13 forest cho thấy vì sao NI theo từng agent thất bại; E12 bảng ⇔ coverage), đọc trực tiếp từ các report được claim table trích dẫn.
- **Đề xuất hướng mới (chưa chạy, chờ bạn quyết):** [PROPOSAL_SPAT_CONTRACT_20261004.md](PROPOSAL_SPAT_CONTRACT_20261004.md).
  - Đội xe có SPaT dưới đèn fixed-time; văn liệu cho lợi ích thật, tới −18 % xăng.
  - Nâng cấp đèn lên đèn học thì SPaT vỡ.
  - Cách sửa: đèn mới giả lập hợp đồng SPaT cũ bằng cam kết (legacy-view emulation phía vật lý, dùng lại Q5), so với guard phía xe và retrain.
  - Collision liền kề (dự báo SPaT, eco-driving bền với sai số) đã ghi.

## 1c. Cập nhật 08:4x (sau khoảng trống do giới hạn sử dụng; hai lần wake 07:41 và 08:41 bị lỡ, spool vẫn chạy hết)

- **B6-R làm sạch (v6, ngân sách ×4):**
  - Không recipe nào đạt B6-1 (fuel tốt hơn và TL không thua).
  - Recipe CoTV **nhanh hơn** mô hình lái của SUMO (TL −2.05 / −2.18, city −1) nhưng tốn thêm xăng +1.5…+1.8 %.
  - v3 với ngân sách ×4 tiến về ngang baseline (trước đó +8…+63).
  - Residual và behavior cloning vẫn tệ.
- **B6-T (đăng ký SAU khi thấy số, gắn nhãn hậu kiểm):** đội xe "có lợi về thời gian" (TL tốt hơn, xăng không tệ hơn 2 %). Chỉ được xác nhận trên seed policy mới 213/313 và traffic mới 400–409; job 046 đang chạy.
  - Nếu đạt, job 047 chạy nghiên cứu nâng cấp đèn A-L\* trên đội xe đó.
  - Smoke 1 seed: đội xe CoTV dưới đèn học RL-H **không suy giảm** (22.09 so với always-SUMO 22.08).
- **Thăm dò 041–045 (đội xe không có lợi, chỉ cơ chế):**
  - cổng đặt đúng chỗ thắng override ngẫu nhiên cùng tỷ lệ, nhưng always-SUMO vẫn thắng;
  - replay vòng hở bác D-1 và D-2;
  - đèn RL-H thắng MaxPressure (baseline đã công bố) khoảng 0.8–1.0 s/veh.

## 2. Kiểm tra tính đúng đã làm

- Trace reward v2 và v3: 12 run đủ horizon, khoảng 3 triệu transition, 0 sai. Ba quy ước (xe đến đích, lỗi API, gap) **chưa bao giờ xảy ra**, nên là nhánh code chưa được kiểm.
- Replay vòng hở trùng trace từng giây (phase, spent, digest hành động).
- `always` = run toàn người, bit-identical.
- Đối chiếu fuel / time loss với bộ đếm của SUMO: nhất quán (fuel lệch ≤ 0.5 %).

## 3. Đang chạy / kế tiếp (cây quyết định đã đăng ký trước)

- **039:** chẩn đoán "baseline nằm trong policy class" (hành động release, residual quanh SUMO).
- **Hàng đợi hiện tại:** 040 (B6-R v5, nhãn "unsanitized") → 040b (residual v6) → 040c (B6-R cả 4 arm bằng v6) → 040d (B6-I behavior cloning) → 041–045. Ước tính xong khoảng 08:30.
- **040 (tự sinh theo kết quả 039):**
  - nếu một class đạt → xác nhận B6-2 (seed mới, traffic 400–409);
  - nếu không → screen recipe B6-R (ngân sách ×4, reward CoTV đã công bố).
- **041–045:** thăm dò trên các đội xe hiện có (chỉ để hiểu cơ chế, không phải bằng chứng triển khai).
- **Giữ lại** adapter / DC-Ada / handoff cho tới khi có đội xe có lợi.

## 4. Đĩa

Ngưỡng 15 GB đã chặn spool lúc 05:49. Tôi đã **lưu trữ (không xoá)** 553 thư mục `scenarios` tự sinh của E3 vào `legacy/scenarios_archive_20261004/` (nén khoảng 13×, kiểm số file khớp trước khi gỡ bản gốc). Đĩa lên khoảng 24 GB.

Ngoài ra có hai thư mục không thuộc dự án mà tôi không đụng tới: cache cập nhật VSCode 1.9 GB và `~/.codex` 2.8 GB.

## 5. Trạng thái chương trình hai quần thể (bản nháp 08:50; điền kết quả B6-T và A-L\* khi có)

**Đã xác lập (kèm bằng chứng):**
1. Đèn học (RL-H) có lợi thật với xe người: +2.5…+2.75 s/veh so với ACT, và hơn MaxPressure (baseline đã công bố) khoảng 0.8–1.0.
2. Các đội xe học theo recipe cũ (Q7/Q7b) **không** có lợi so với mô hình lái của SUMO. Lý do là reward bị lợi dụng (v1: lệnh tăng tốc khi đứng; v2: bò).
3. "Hại khi nâng cấp đèn" có thật với một số đội xe đó (L-ACT_0, _2): hại do đội xe quyết định, cơ chế là phanh ngoài support. Cổng phản ứng đặt đúng chỗ giảm hại và thắng override ngẫu nhiên cùng tỷ lệ, nhưng **tắt đội xe vẫn tốt hơn**.
4. Với ngân sách ×4 và reward CoTV, đội xe RL **nhanh hơn** SUMO khoảng 2 s/veh nhưng tốn thêm 1.5–1.8 % xăng trên SELECT. B6-T đang xác nhận trên seed và traffic mới.

**Đã bị bác hoặc không được hỗ trợ:**
- hidden queue (HC-1);
- co-training tạo partner-specificity (C-2);
- reward delay giúp (C-3);
- "bất đối xứng" về phản ứng (D-2);
- guard vô hại với đội xe bền (G-L3);
- E14 (OP > FT-mix).

**Đích đã dịch chuyển:**
- Nếu đội xe có lợi (F\*) **không** suy giảm khi đèn nâng cấp (AL\*-1 âm), thì vấn đề tương thích hai quần thể **không tự phát sinh** với đội xe được đặc tả tốt trong môi trường này. Độ mong manh trước đây là triệu chứng của reward bị lợi dụng. Đó là một kết quả có giá trị, nhưng không phải kết quả "phương pháp thắng".
- Khi đó hướng có nội dung là hướng mà đội xe **phụ thuộc thông tin từ đèn** (SPaT): nâng cấp đèn phá giao diện đó theo cấu trúc, và legacy-view emulation (đèn cam kết SPaT cũ) là phương pháp đúng mạch. Xem [PROPOSAL_SPAT_CONTRACT_20261004.md](PROPOSAL_SPAT_CONTRACT_20261004.md); cần bạn quyết.

**ETA cập nhật:**
- Paper E3 (legacy-view): đã có claim table, 3 hình, khung bản thảo biên dịch được, Lean E9 và E12-a đã qua gate. Còn: kiểm ngoài (cần quyền tải), viết đầy đủ. Khoảng **2–3 ngày**.
- Paper hai quần thể: phụ thuộc quyết định hướng SPaT; nếu đi tiếp, khoảng **5–7 ngày** (B6 với SPaT → nâng cấp → xác nhận → Cologne8).

## 5b. Cập nhật 09:05 (wake 8, trong lúc chờ 046)

**Comparator mới, đăng ký trước khi có dòng kết quả nào của B6-T (C-25; PROTOCOL_CITY_B6 §B6-Z):**
- **Lớp residual không chứa SUMO.** Khi xe đang bị `setSpeed`, `getSpeedWithoutTraCI` không bao giờ vượt tốc độ đang ra lệnh. Vì vậy δ = 0 nghĩa là "không bao giờ tăng tốc": probe cho thấy xe dừng đèn đỏ đứng yên cả khi đèn đã xanh. Smoke δ = 0: TL +274 s/veh. Phát hiện này chỉ ảnh hưởng 039 (vốn đã VOID) và 040b.
- **Đường release đúng:** smoke Z-rel trùng always-SUMO ở mọi đại lượng.
- **Comparator "tài xế hoàn hảo" Z-sig0** (SUMO tự lái các xe agent, σ = 0). Smoke một seed: agent TL −4.4 s/veh, xăng +2.1 %. Hồ sơ này **rất giống R2/R3** (TL −2, xăng +1.5–1.8 %). Lợi thế thời gian của đội xe học có thể chỉ là việc bỏ imperfection của SUMO. *[ĐÍNH CHÍNH §7: σ = 0 chỉ là Krauss không có imperfection, không phải tài xế tối ưu]*
  - Quy tắc câu chữ Z-4c đã đăng ký: nếu fleet đạt B6-T nhưng không nhanh hơn Z-sig0, chỉ được viết "nhanh hơn tài xế SUMO mặc định (có imperfection), không nhanh hơn chính mô hình đó khi bỏ imperfection".
  - Job 046z chạy ngay sau 046.

**Paper legacy-view:**
- Bản nháp v2 đã biên dịch: thêm mở đầu với hợp đồng `D_i(T^U_i(h_t)) = v^K_i(h_t)`, mục setting, bảng E7 chép thẳng từ report, và related work.
- Bản nháp nêu thêm một kết quả bất lợi: **mixed fleet có emulation vẫn thấp hơn retrain toàn bộ fleet**, EMU − ALLNEW = −0.59 [−1.35, −0.02].

## 5c. Kết quả 09:14: B6-T và B6-Z

**B6-T NOT CONFIRMED** (C-26). Cả bốn fleet trên seed mới và traffic 400–409 đều FAIL. R3 nhanh hơn always-SUMO trên cả hai seed (−1.19 và −2.09 s/veh), nhưng mỗi seed trượt một ràng buộc phụ: t2 trượt human TL (upper +0.83 > 0.5), t3 trượt xăng (upper +2.07 % > 2 %). R2 không ổn định giữa các seed (t2 chậm hơn +2.70). Theo quy tắc đã đăng ký, B6 vẫn âm và không chạy A-L* (047 / 048 tự thoát).

**B6-Z** (C-27):
- release ≡ always-SUMO (exact);
- residual δ = 0 làm kẹt toàn mạng: lớp residual không chứa SUMO;
- **SUMO σ = 0, không học gì, nhanh hơn always-SUMO 5.2 s/veh, tốn thêm 2.6 % xăng;**
- **mọi fleet học đều chậm hơn tài xế SUMO hoàn hảo đó 3–8 s/veh.** *[ĐÍNH CHÍNH §7: "SUMO σ = 0", không phải "hoàn hảo"]*

Câu được phép viết: *"Trong panel đã thử, không có đội xe học nào đạt tiêu chí lợi ích đã đăng ký so với mô hình lái của SUMO; lợi thế thời gian thấy trên SELECT không lớn hơn việc bỏ imperfection của tài xế SUMO."*

**Bước 4 của bạn (recipe / horizon / baseline):**

| Phần | Trạng thái |
|---|---|
| recipe | B6-R, xong |
| baseline | B6-Z, xong; B6-S là biên của họ σ, đang chạy |
| horizon | B6-H, đăng ký 09:13; trace check v7 PASS; đang xếp hàng, khoảng 35 phút |

Dự đoán đã đăng ký: không fleet B6-H nào đạt và không fleet nào vượt họ σ. Nếu đúng, bước 4 đóng, và hướng kế tiếp là thông tin (SPaT), cần bạn quyết.

## 5d. 09:17: B6-S, biên của SUMO không học (C-28)

- SUMO lái các xe agent với σ thấp hơn mặc định là **vừa nhanh hơn vừa tiết kiệm hơn**. Ví dụ σ = 0.3: −2.5 s/veh và −2.2 % xăng; lặp lại trên traffic 400–409.
- **Fleet học nào cũng bị một mức σ nào đó dominate.** Tiêu chí S-2 đã đăng ký trước khi chạy. *[ĐÍNH CHÍNH §7: nhãn sai logic; kiểm lại thì 11/12 fleet bị dominate thật, R4v6_t1 chỉ là chưa tách được]*
- Hệ quả: always-SUMO (σ = 0.5) là comparator yếu cho đội xe ra lệnh tốc độ. Mọi claim về đội xe sau này dùng S-2.

**Thí nghiệm mới, đã đăng ký và xếp hàng (049c, B6-SL):**
- Fleet σ = 0.3 là một "đội xe có lợi" thật, dù không học. Thí nghiệm đặt nó dưới đèn học RL-H giữ nguyên để đo tương tác nâng-cấp-đèn × nâng-cấp-xe; đây là ô "light frozen, fleet upgraded" của thiết kế 2×2.
- Dự đoán đã đăng ký: lợi ích giữ được, và |tương tác| trên city TL < 0.5 s/veh.
- Smoke 600 s một seed đã xem (khai báo trong protocol).

## 5e. 09:42: B6-H (horizon) và B6-SL

**B6-H (C-29).** Một trong sáu fleet đạt B6-1: **R5h_t0** (reward v3, release, horizon cả chuyến): xăng −3.9 %, TL −0.65, không hại xe người. Đây cũng là fleet học đầu tiên **vượt họ σ**. Seed t1 cùng recipe thì FAIL. Theo quy tắc phải đạt cả hai seed, R5h chưa phải candidate. Dự đoán "không fleet nào vượt họ σ" của tôi **sai ở một seed**. Hiệu ứng horizon không nhất quán giữa các seed. *[ĐÍNH CHÍNH §7: "nối các approach", không phải cả chuyến]*

**B6-SL (C-30), cả hai dự đoán SUPPORTED.** Nâng cấp đội xe không học (σ 0.5 → 0.3) dưới đèn học RL-H giữ nguyên:
- lợi ích giữ nguyên (TL −2.70, xăng −3.11 %);
- tương tác trên city TL là −0.16 [−0.43, +0.09];
- lợi ích xăng còn **lớn hơn** dưới đèn học.

Nghĩa là trong khoảng này, đèn học **không** đặc thù với mô hình lái của SUMO. Cái hại thấy trước đây khi nâng cấp đèn đến từ các fleet học bị reward loophole, không phải từ việc nâng cấp xe nói chung. *[ĐÍNH CHÍNH §7]*

**Đang chạy (050r, B6-R5, đăng ký 09:39).** Replicate R5h trên 4 seed policy mới, traffic mới 410–419 (tạo cục bộ, đã kiểm tái tạo bit-identical seed 400), có họ σ trên cùng traffic. Verdict pooled gồm ba phần: B6-1, S-2 và ràng buộc teleport trên từng seed.
- **Nếu đạt:** R5h là F\*, một fleet học có lợi về xăng, và nghiên cứu nâng cấp đèn với F\* cần một đăng ký riêng.
- **Nếu không đạt:** bước 4 đóng.

## 5f. 10:02: B6-R5, bước 4 đóng

**R5h NOT CONFIRMED (C-31).** Trên 4 seed mới và traffic mới 410–419, R5h tiết kiệm xăng ổn định (pooled −3.3 %, seed nào cũng tiết kiệm) nhưng **chậm hơn** (+3.0 s/veh), có hại nhỏ cho xe người, và seed t2 có teleport. Cả 4 seed đều FAIL B6-1. R5h vượt họ σ chỉ nhờ đổi thời gian lấy xăng. Seed t0 lặp lại kết quả đạt trên traffic mới, tức là đây là một seed may mắn.

**Lưu ý phương pháp (C-29b):** reward lúc train của seed đạt và seed trượt gần như trùng nhau, nên không chọn được seed tốt bằng reward train. *[ĐÍNH CHÍNH §7]*

**Bước 4 của bạn đã đóng:**

| Phần | Kiểm bằng |
|---|---|
| recipe | B6-R |
| horizon | B6-H |
| baseline | B6-Z, B6-S |

Kết luận: không có đội xe học nào có lợi trong không gian quan sát này. Theo thứ tự bạn đặt, **không đổ thêm công vào adapter, gate hay handoff** cho đội xe học ở đây (060 / 070 / 095 vẫn hold). *[ĐÍNH CHÍNH §7: quá mạnh; xem cách viết đúng ở §7]*

**Đang chạy:** 052v, xác nhận C-30 (nâng cấp xe không học × đèn học) trên VALIDATION 200–209, khoảng 3 phút.

## 5g. 10:11: kết quả dương, nâng cấp đội xe dưới đèn học giữ nguyên

**T4 xác nhận trên VALIDATION (C-32).** Nâng cấp σ 0.5 → 0.3 dưới RL-H: lợi ích giữ nguyên (TL −2.81, xăng −3.26 %), tương tác city TL −0.17 [−0.48, +0.12].

**T5, đội xe tự động hoá (ACC của SUMO, không học) (C-33).**
- Không bị đèn học làm hại; ngược lại, hai nâng cấp **siêu cộng tính**: tương tác −0.83 [−1.17, −0.52] trên VALIDATION.
- Gain của đèn học tăng từ −2.41 lên −3.24 s/veh khi đội xe là ACC.
- Dự đoán "trong ±0.5" bị bác theo chiều có lợi.
- ACC tốn thêm 5–8 % xăng.

**Hình chung:**
- Đèn học **không đặc thù với mô hình lái** khi đội xe được nâng cấp bằng mô hình lái tốt hơn.
- Cái hại thấy trước đây (C-14 / C-16) chỉ xuất hiện với các đội xe **học** có reward bị lợi dụng. *[ĐÍNH CHÍNH §7]*
- Trong không gian quan sát này, chưa đội xe học nào tốt hơn các mô hình lái không học.

**Đang chạy (054, B6-G):** cùng câu hỏi dưới hai họ đèn học khác: RL-C50, và RL-J (train cùng đội xe học L-ACT).

## 5h. 10:19: B6-G và mạng thứ hai

**B6-G (C-34), dự đoán SUPPORTED.** T4 / T5 đúng cho cả hai họ đèn học khác:
- RL-C50;
- RL-J, được train cùng đội xe học.

Không có hại ở 4/4 ô. ACC siêu cộng tính ở cả ba họ đèn (khoảng −0.8 s/veh).

**Cologne8, RESCO (C-35):**
- Recipe đèn học của grid4 **thua** fixed-time của mạng này: +4.79 s/veh. T1 không lặp lại.
- T4 / T5 chưa kết luận được: điểm ước lượng ≈ 0 nhưng CI ±2, chưa đủ lực, và lại dưới một đèn không có lợi.
- Muốn kiểm T4 / T5 ở đây cần một đèn có lợi trên cologne8 (train lâu hơn hoặc MaxPressure) và nhiều seed hơn.

## 6. Tóm tắt cuối đêm (viết 10:20; G4-L2 điền khi xong)

**Câu trả lời cho câu hỏi của reviewer** (nâng cấp đội xe, đèn giữ nguyên; sửa quan sát của đèn hay phản ứng của xe):

| Đội xe | Kết quả | Ledger |
|---|---|---|
| Không học, nâng cấp mô hình lái (σ thấp hơn, ACC) | Đèn học giữ nguyên **không hại**, ở cả 3 họ đèn học và 2 panel traffic. Với ACC còn có lợi thêm khoảng 0.8 s/veh (siêu cộng tính). Không cần sửa gì ở cả hai phía. | C-30, C-32 … C-34 |
| Học | Trong không gian quan sát này, chưa có fleet nào **có lợi** so với mô hình lái không học, dù đã thử hơn 10 recipe (v2, v3, release, residual, BC, R1–R4, R3h, R5a, R5h) với nhiều seed, reward CoTV, ngân sách ×4, hai horizon. Vì vậy câu hỏi "sửa phía nào" cho đội xe học chưa có đối tượng hợp lệ. | C-21 … C-31 | *[ĐÍNH CHÍNH §7]*
| Học, có hại khi đèn nâng cấp (L-ACT) | Sửa **phản ứng** phía xe giúp rõ, clip quan sát τ thì không (trong panel đã thử). Nhưng tắt đội xe còn tốt hơn. | C-14, C-16 |

**Bài học phương pháp có bằng chứng:**
- 4 bẫy: reward đọc lệnh, sentinel teleport, ratchet của `getSpeedWithoutTraCI`, comparator σ.
- Reward lúc train không chọn được seed tốt. *[ĐÍNH CHÍNH §7: chỉ statistic `mean_r` đang log là không phân biệt được]*
- Họ σ là biên mà mọi đội xe phải vượt.

**Mạng thứ hai (cologne8):** recipe đèn của grid4 không có lợi ở đó: thua FT +4.79 ở 120 episode, và +15.10 ở 480 episode (C-35, C-36). Vì vậy T4 / T5 chưa kiểm được trên mạng này. Cần recipe đèn khác, ví dụ agent đã công bố của RESCO; việc này phải đăng ký riêng.

**Paper legacy-view (E3):** bản nháp v2 biên dịch được; số liệu khớp claim table; có nêu kết quả bất lợi EMU − ALLNEW.

**Cần bạn quyết:**
1. **Hướng SPaT** (`PROPOSAL_SPAT_CONTRACT_20261004.md`), đã nâng bar lên "vượt họ σ". Hoặc biến thể rẻ hơn: GLOSA không học làm quần thể xe.
2. **Câu chuyện paper hai quần thể:** đi theo T4 / T5 cộng các bẫy (M1)? Hay chờ SPaT?
3. Ghi chú phương pháp về các bẫy SUMO, ở mức workshop: có làm không?
4. Commit: rất nhiều thay đổi chưa commit (ledger, protocol, script, kết quả). Tôi chỉ commit khi bạn bảo. Dữ liệu RESCO / CoLight không được commit.

## 7. Đính chính theo audit `CITY_B6_FINAL_AND_SPAT_AUDIT_20261004` (12:04; ledger C-37; raw và verdict giữ nguyên)

Tôi đã đối chiếu từng điểm với code và đồng ý cả sáu. Các dòng bị sai trong báo cáo này được đánh dấu *[ĐÍNH CHÍNH §7]*; nội dung gốc giữ nguyên để làm lịch sử.

| # | Câu cũ | Cách viết đúng / bằng chứng |
|---|---|---|
| A | "Không có đội xe học nào có lợi trong không gian quan sát này" | **"Chưa có recipe học nào được XÁC NHẬN đạt đồng thời: tiết kiệm xăng, TL không vượt ngưỡng, không hại xe khác, trong thiết lập đã thử."** R5h_t0 (checkpoint phát triển) đạt B6-1 trên traffic mới, nên có policy khả thi trong lớp hiện tại. Chưa phân lập được nguyên nhân: thông tin, mục tiêu huấn luyện, hay độ ổn định tối ưu hoá. **Không** suy ra SPaT là bắt buộc. Không dùng t0 để đổi verdict R5h. |
| B | "Mọi fleet học bị họ σ dominate" | Nhãn của reporter sai logic: không chứng minh thắng ≠ chứng minh thua. Kiểm lại từ raw, đòi σ tốt hơn có ý nghĩa ở **cả hai** trục (mô tả, chưa hiệu chỉnh): **11/12 fleet của C-28 bị dominate thật; R4v6_t1 chỉ là chưa tách được.** R5h pooled VƯỢT họ σ; theo seed 4/6 vượt, 2/6 chưa xác lập, 0 bị dominate. Phép OR hai kiểm định một phía không phải kiểm định 5 % tổng thể. |
| C | "Horizon cả chuyến" | Đổi thành **"nối các approach"**. Đo từ log: khoảng 0.98 terminal mỗi chuyến, tức mọi approach có đèn đều được nối. Không tính chi phí: đoạn ra sau đèn cuối, khoảng 2 % chuyến bị cắt ở 3600 s, và khoảng teleport. |
| D | "Reward train không chọn được seed tốt" | Chỉ là: **statistic `mean_r` đang log** (trung bình reward theo transition) không phân biệt được hai seed. Nó không phải return theo chuyến. |
| E | "`invalid = 0`" | Chưa loại trừ mọi lỗi API: exception và edge rỗng trả 0 mà không đếm; khoảng teleport được nối với một bước discount. Quy ước thực tế và các counter cần cho trainer kế tiếp: `research/city_sim/FLEET_MDP_CONVENTIONS_V6_V7_20261004.md`. |
| F | "Cái hại cũ đến từ reward bị lợi dụng" | **"Hại thấy ở các fleet học yếu / fragile. Với các nâng cấp σ / ACC đã thử, chưa thấy tương tác có hại theo endpoint. Nguyên nhân chưa được phân lập** bằng so sánh hai nhóm này." |
| — | "Tài xế hoàn hảo" (σ = 0) | **"SUMO Krauss không có imperfection (σ = 0)"**, không phải tài xế tối ưu. |

**Phần SPaT** cũng được đính chính trong proposal (mục "Đính chính"):
- `getNextSwitch` không phải time-to-green của movement;
- 1e5 là artifact của cách cài đặt, không chứng minh "không thể dự báo";
- cam kết pha không phải emulator E3;
- adaptive-SPaT đã có prior art;
- giá của commitment đã thấy ở Q5.
