# MARL — bản cập nhật cho agent dừng ở 28–29/09 (DFL / F1 / S1–S4 / critic), so với MARL v1
# (viết 02/10/2026 23:1x EDT; nguồn: MARL_SELF_AUDIT_LEDGER_20260928.md L-66 … L-289, CITY_LEDGER_20261002.md C-1 … C-7,
#  MARL_LESSONS_AND_STORY_20261002.md, FAILURE_SYNTHESIS_20261002.md, DAY_SUMMARY_20261002.md)

## 0. Bạn đang ở đâu
Trạng thái cuối của bạn ≈ ledger L-66 … L-90 (28/09 tối – 29/09 chiều): DFL không qua sàng lọc (scratch s3 +0.42
[−1.69, +2.57] vs prefix; dense −0.025; BC s3 +0.11), F1 (label dày) không cải thiện lặp lại được, S1–S4, guarded reruns,
critic pair accuracy ≈ 0.50–0.56, L-86 sửa lời đọc "needle regime" quá đà, và hai lối bạn đang cân nhắc: (a) học giá trị có
cấu trúc receiver–sender, (b) certificate để giảm truyền mà vẫn giữ quyết định (certificate lifetime / selective maintenance).
**Cả hai lối đó KHÔNG được theo tiếp.** Chương trình "chọn message cho actor đóng băng" (E3 của MARL v1) đã bị bỏ ở 29/09
tối sau hai control quyết định (mục 1).  Mọi thứ sau đó dùng một thước đo khác: **compiled silence**.

## 1. Vì sao chương trình selector / critic / DFL của v1 bị bỏ (29/09, L-105 … L-117)
* **L-105 (quyết định):** actor train KHÔNG có message (0 B) tốt hơn MỌI actor prefix (−8.0 % [−8.6, −7.4] vs hệ prefix
  188.7 B/step); actor full-info dưới full delivery −10.5 %.  Giá trị của thông tin láng giềng cho một actor ĐÃ TRAIN chỉ
  ≈ 2.5 % và chỉ khi delivery đầy đủ, nhất quán → tối ưu việc chọn message cho actor prefix đóng băng là tối ưu sai đối tượng.
* **L-114 / L-115:** baseline MP2 bị lỗi đặc tả — dùng message làm nó tệ hơn 14 % so với `maxq` (cùng luật, không message).
  Claim A1 của v1 ("max pressure tệ hơn 9.5–24 %") bị SỬA: so với maxq, actor BC THUA (+1.2 … +5.5 %), actor scratch chỉ thắng
  2–6 %.
* **L-117 (tự phê bình):** thiếu hai control mà corpus đòi: actor không-giao-tiếp train cùng chế độ, và audit bộ điều khiển
  tham chiếu.  Từ đó: mọi giao tiếp phải thắng một **zero-byte student Z chưng cất từ CÙNG teacher full-info** (MARL v2).
* Chương trình cũ được dời vào phụ lục "History: scheduling messages for frozen actors" của paper_marl_v2.tex.

## 2. Dòng thời gian sau đó
| Ngày | Kết quả (ledger) |
|---|---|
| 29/09 tối – 30/09 sáng | Các test đăng ký trước vs Z: **BYTEBUDGET** (3 B tóm tắt quyết định, 27 B/step) thắng Z −3.6 % [−4.5, −2.7], 5/5 seed, cả OOD, codebook B, 25 % mất gói (L-160); TRAINEDQ4 mong manh (seed 2 +5.1 %); FO, FOSTUDENT, SETFRESH không qua; control: gain = THÔNG TIN của teacher (no-comm teacher +0.2 %, L-149); nguyên nhân gốc: actor slot-indexed phẳng gặp hiện diện thưa → set actor |
| 30/09 | **RELAY** (bảng 3 B được relay trong gói HETERO_v0, student chưng cất) thắng Z (L-163); head theo congestion bỏ đói phần đuôi → head **age-first / xoay vòng** sửa được capacity thấp (L-169, L-175); bài học V-U tautology: null bằng Z′ (excess +0.19 … +0.34, L-178); deadline/EDF head âm; lưới 4×4 qua wrapper (L-186) |
| 01/10 | Panel dự trữ 10 seed: **relay age-first thắng Z** iid −2.29 %, cap4 −2.04 %, low −1.26 %, mọi upper < 0 (L-201); thứ tự quan trọng: congestion order mất lợi thế ở capacity thấp (L-202); predictor P1b fail, flagship thu hẹp (L-207); **đảo dấu K = 1**: receiver train iid THUA Z ở K = 1 hằng; clip (+0.79) và gate freshness (+0.78) chỉ gỡ một nửa (L-211, L-221); receiver floor CHỨNG MINH trong Lean (L-224, L-227); khung compatibility (L-230) |
| 02/10 | **"support, not freshness"**: mismatch law E1 (L-249); train-match cứu (L-250); chung cho 3 kiến trúc (L-252); mixture (L-256); W1 law replicate (L-258) nhưng prospective chỉ giữ thứ tự (L-282); testbed remote-inference (L-261, L-263, L-265); mọi sửa ở input fail (L-266, L-274, L-279); double dissociation 3×3 tuổi / 4×4 coverage (L-268, L-272); **mạng thứ hai 4×4** replicate, rule A training-relative 3/3 prospective (L-270); support > distance ở cùng W1 (L-277); H-RID (L-278); kênh đổi giữa episode (L-285); 4×4 train-match +5.80 / upgrade −3.55 (L-286); test C: trộn hai cực an toàn nhưng không phủ giữa (L-287) |
| 02/10 tối | Số 3 — fallback support về Z (L-288, đang chạy); số 4 — NYC 16×3 mạng thứ ba (L-289, đang chạy); test D (4×4 mixture) đang chạy; city track C-1 … C-7 (Q7: đèn RL tốt hơn 11 % nhưng làm fleet xe học đã triển khai hỏng, compatible mode sửa) |

## 3. So với MARL v1
| v1 nói | Bây giờ |
|---|---|
| Lý thuyết: committed priorities, bounded revision, paid bids (Lean) | vẫn đứng như lý thuyết; không thí nghiệm nào mới đụng tới; city Q5 (commit/revise cho đèn) cho thấy commitment có GIÁ thật ở demand chưa bão hòa |
| E3: selector/critic học được chọn message tốt hơn prefix | **không bao giờ thành lập** (DFL, F1, ranking critics, acquisition arms ≈ 0.50 pair accuracy; offline gain không dự đoán closed loop, Spearman 0.27, L-84) → bỏ |
| A1: MP2 tệ hơn actor 9.5–24 % | **sai do baseline lỗi**, đã sửa (L-115) |
| Hình E3 / số liệu E3 của v1 | không dùng nữa; thước đo mới là Z (compiled silence) |

paper_marl_v2.tex (01/10 10:04, "Fresh Coverage … Relay, Age-First Ordering and a Compiled-Silence Bar") chứa relay + age-first +
thước đo Z + receiver floor, nhưng **LẠC HẬU** với bằng chứng từ 01/10 trưa: đảo dấu K = 1, train-match, upgrade hazard, mạng
4×4, và luận điểm hiện tại "support, not freshness" (tiêu đề "Fresh Coverage" đi ngược luận điểm này) — chưa viết lại.

## 4. Đã thử và SAI (đã đăng ký trước, fail)
* Chọn message học được: DFL, F1, critic, acquisition — không thắng prefix (L-66, L-75, L-79, L-84).
* FO / FOSTUDENT / SETFRESH; TRAINEDQ4 ở 5 seed; deadline/EDF head (L-178); predictor P1b (L-207); luật N_s, teacher margin,
  net_Z (không chuyển sang 4×4, L-270); gate freshness "không bao giờ tệ hơn Z" (GT1); clip "về bằng Z" (A2).
* Sửa ở input của receiver: age remap (L-266), onefresh (L-274, GTM5), time projection (L-279), clip trên 4×4 (G4), clip trong
  testbed RI (L-285) — **mọi relabel giá trị trong dải đều hại**.
* W1 như định luật định lượng (L-282: chỉ giữ thứ tự); mixture = hợp các specialist (MX3, phụ phí ≈ 1 điểm); trộn hai kênh cực
  phủ kênh giữa (C1, L-287).
* City: certificate chỉ từ log của đèn (Q7-3); certificate tổng hợp K < S_exit (C0b-2); semantics/CUT (C0); cửa sổ commitment
  rẻ (Q5); sửa phía đèn cho eco-driving (Q2b B3).
Tổng hợp nguyên nhân và giả thuyết mới: FAILURE_SYNTHESIS_20261002.md (F1–F6, H1–H5).

## 5. Đã BỎ (quyết định, không phải chỉ fail)
Chương trình selector/critic/DFL; hai lối (a) giá trị receiver–sender, (b) certificate lifetime / selective maintenance
(phần "giữ cache" sống lại dưới dạng hold experiments: count-deadline scheduler không có chỗ, L-240; LeanMarlHoldFloorV1);
MP2 làm tham chiếu (thay bằng maxq và Z); lời đọc "needle regime" (L-86); biến thể in-protocol HETERO_v0; SafeEdit probe (rút,
L-229); claim V-U dạng tách Z ≠ T (tautology); flagship predictor N_s (thu hẹp); mọi sửa ở input; W1 như đòn bẩy.

## 6. Đã THÀNH CÔNG (đứng vững)
* Relay + head age-first thắng compiled silence trên panel dự trữ 10 seed (L-201), cả ở 4×4 (+6.26 / +5.78 / +2.93 %, L-270).
* BYTEBUDGET thắng Z 5/5 seed (L-160).
* Đảo dấu K = 1 (receiver train iid thua Z ở kênh nghèo) — 3×3 nhiều panel, 4×4 (−2.41, −2.58).
* Train-match cứu receiver (3×3 L-250; 4×4 +5.80 [4.38, 7.15], 10/10 seed); upgrade hazard: kênh TỐT HƠN làm receiver train
  ở kênh nghèo TỆ đi (P-UP2; 4×4 −3.55).
* Mixture cứu (MX1, MX2), theo dõi kênh đổi giữa episode (SW1, SW2), nhận ra regime (H-RID).
* Support > distance (L-277); double dissociation của thống kê ngoài support (L-272); rule A training-relative prospective
  3/3 trên 4×4 (L-270).
* Lean sạch (axiom chuẩn): ReceiverFloor, MismatchW1, Emulation, Provisioning(+Instances), Support, HoldFloor, Mixture,
  AgeRole, Projection; City: ConditionalShift, InfoFundamental, **ReceiverContract (02/10 23:1x: no_receiver_free_certificate,
  order1_blind_pair, order2_blind_triple)**.  Full gate (315 module) CHƯA chạy lại (dừng ở 33/315 theo lệnh user).

## 7. Luận điểm hiện tại
"Support, not freshness": giao tiếp có giúp một receiver đã học hay không là do view lúc triển khai có nằm trong TRAINING
SUPPORT (joint) của nó; mạng dự đoán được chỗ support vỡ (floor, provisioning, rule A); emulation được khi nâng cấp, không
được khi hạ dưới floor; cách sửa bền là đổi support (train khớp hoặc mixture), không phải đổi input.
Mở rộng city (sau 2 review ngoài đã verify, CITY_TWO_POPULATION_NOVELTY §7): compatibility CÓ HƯỚNG và phụ thuộc receiver
(U ⇝ R); không certificate nào bỏ qua receiver đúng cho mọi receiver (T1, Lean); certificate có thể cần bậc tương tác ≥ 2
(T3, Lean; Q4 là witness s = 2); hai cách sửa đối ngẫu — phía receiver (fallback) và phía producer (compatible mode, Q7).
Prior art phải cite: SIL-C (NeurIPS 2025), Assume-Guarantee RL (AAAI 2024), Bansal 2019, Träuble 2021, Yu et al. ICAPS,
Gama 2012.14906 / NeurComm (relay), Johansson–Sontag–Ranganath 2019.

## 8. Đang chạy (02/10 23:1x) và việc mở
* Test D (4×4 relayMIX, 10 seed, nohup) — ≈ vòng 110/500, mỗi lane 2 seed nối tiếp.
* Số 3: fallback support (PROTOCOL_E3_SUPPORT_FALLBACK_20261002 + Addendum 1–2), 5 lane, panel 4801 / 4901.
* Số 4: NYC 16×3 (PROTOCOL_E3_NYC16X3_20261002), 5 teacher; lưới cách điệu + tuyến taxi thật.
* City Q7b (replication 3 seed train mới, frontier, certificate theo contract): đã viết, đang smoke.
* Mở: viết lại paper_marl_v2 theo "support, not freshness"; full Lean gate; truy nguồn τ_train = 9 của Addendum 4 (đo lại = 4).
* Giới hạn: tất cả là mô phỏng với thành phần tự train; chưa có log controller thật, trace J2735, stack độc lập, dữ liệu
  cross-version thật.

## 9. Quy tắc làm việc đang áp dụng
Protocol trước khi chạy; novelty check trước khi build; smoke trước; `python -u`; không sửa script đang chạy; không xóa (dời
vào legacy/); không kill process trừ khi user bảo; job dài chạy nohup từ terminal của user (job run_in_background chết khi
phiên thoát — 22:08 hôm nay); chỉ commit khi được bảo; báo cáo tiếng Việt; chạy `date` trước khi ghi giờ; không sửa ROADMAP /
OPEN_MATH / THEOREM_MAP; không đưa gì vào manuscript như định lý trước Lean gate; subagent chỉ khi user nói "fetch".
Đọc trước: DAY_SUMMARY_20261002.md, MARL_LESSONS_AND_STORY_20261002.md, FAILURE_SYNTHESIS_20261002.md, ledger L-249 … L-289.
