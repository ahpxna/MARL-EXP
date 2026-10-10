# Tìm collision cho paper TSI hai quần thể (06/10/2026, 20:59)

Bằng chứng gốc (truy vấn, ghi chú trang, kết quả agent, đoạn trích Genser) nằm trong `collision_20261006/`.
Bản này bổ sung bảng collision trong `PUBLICATION_READINESS_TSI_20261006.md` (sáng 06/10).

## 0. Kết luận

**Không có collision FULL** cho đóng góp nào. Có một phát hiện buộc phải sửa chữ: cơ chế "xe dùng dự báo làm thay đổi detector,
nên dự báo học offline hỏng" đã được Genser et al. nêu định tính (bài đã trích, nhưng chưa trích cho điểm này). Câu "what is new here is
their instance at the signal–eco-driving interface" trong mục The Gap phải hẹp lại.

## 1. Đã làm gì, phủ tới đâu

- Hai lượt sweep 16 agent (10:54 và 15:52) đều chết vì giới hạn phiên trước khi báo cáo. 8 agent chạy được đã làm 345 truy vấn và đọc
  khoảng 120 trang. Tôi trích từ transcript 1758 link, lọc còn 708 tiêu đề liên quan và rà tay (`triage_titles.txt`).
- 8 agent tìm có giới hạn (20:52–20:58; mỗi agent ≤ 10 search, ≤ 5 fetch): bằng sáng chế, lần trích dẫn (adapter; SPaT), tiếng
  Trung/Đức, luận án và báo cáo, hội nghị 2025–2026, tương thích MARL tổng quát, phương pháp/lý thuyết. Khoảng 124 truy vấn.
- Kiểm chứng: khoảng 40 work được đọc qua trang (bản tóm tắt của WebFetch, **một lượt đọc mỗi work, không phải 3 phiếu**). Genser:
  trích nguyên văn từ PDF arXiv v1. Erdmann 2013: đọc full text. Siemens EP3594920A1: đọc trang patent.
- Workflow deep-research: 54/106 agent xong; bước kiểm chứng 3 phiếu còn dở khoảng 51 phiếu. Các claim của bước đọc nguồn dùng ở mục 5,
  ghi rõ là một nguồn.
- Không đọc được: luận án Paine 2025 (trang có kiểm tra chống bot, không vượt), MDPI, ScienceDirect (403). Tài liệu tiếng Trung chỉ
  có metadata.

## 2. Bảng theo đóng góp (cập nhật)

| # | Đóng góp | Verdict | Gần nhất (mới in đậm) | Họ KHÔNG làm gì |
|---|---|---|---|---|
| C1 | Fleet học mất lợi ích khi đèn thành đèn học, không train lại | PARTIAL | Stevanovic 2013; NYSERDA 19-08; Jiang 2022; Paine 2025 (luận án, chưa đọc được); **Erdmann WiVeC 2013** | Không có hai quần thể học bị đóng băng; không đo lợi ích mất so với fleet chuẩn |
| C2 | Dự báo công bố tự phá vì xe glide rời khỏi bộ đếm halting của đèn học | **PARTIAL (nâng mức)** | **Genser et al. T-ITS 2024, mục Discussion** (nêu định tính, actuated, loop detector); **Erdmann 2013** (GLOSA cần kế hoạch ổn định, đèn adaptive làm nó bất ổn); **Ming et al. ITSC 2025** (eco-driving giảm năng lực, gây blockage/spillover); Maadi 2022; Malena ITSC 2025 | Không ai đo hiện tượng (publish vs shadow), không ai chỉ ra kênh halting threshold của đèn học, không ai sửa nó |
| C3 | Dự báo lai: exact khi đã xác định + quantile theo trạng thái; mạng fit trên log thu khi bảng c2 đã được công bố (một bước, Algorithm alg:cal) | COMPONENT (thành phần đã có) | EP3985636 (QRNN quantile); **Eteifa luận án VT 2024** (logic controller + ML, độ tin cậy ensemble); **TTS US10008113B2** (giả lập controller + thống kê); **TTS WO2020086615A1**; **Siemens WO2021110370A1** (phân phối xác suất thời gian còn lại); **Nissan US20170169705A1**; Genser gợi ý học online/meta-learning như hướng tương lai | Tất cả nhắm đèn actuated/adaptive, train offline; không ai dự báo đèn RL và train trên log đã công bố |
| C4 | Adapter đếm theo dải vận tốc trước đèn học bị đóng băng | COLLIDED ở cấp họ phương pháp | DC-Ada; MATES; Huang ICAPS 2026; **RobustLight ICML 2025** và **MDRC arXiv 2609.27528** (module khôi phục quan sát cắm trước đèn RL không đổi); **Siemens EP3594920A1** (tín hiệu detector ảo trước controller không đổi, để GLOSA ổn định); **Sim2Signal 2026** (khoảng cách quan sát sim-to-real); Majstorovic Sensors 2025 (thông tin vận tốc trong state của đèn RL) | Đều xử lý hỏng/thiếu cảm biến hoặc tầm nhìn xa, không xử lý dịch chuyển do quần thể đối tác gây ra; adapter là mô hình học, không phải phép đếm vật lý 2 tham số |
| C5 | Sửa cả hai interface, cả hai policy đóng băng | NOT FOUND trong giao thông; **PARTIAL ở mức ML tổng quát** | Giao thông: chỉ có co-train (CoTV, HONEST-CAV [IEEE IV 2026], Busch, Han TR-C 2026, PriEco-DRL 2026, Uni-Light 2026, Nghiem Appl. Sci. 2026, Chen Appl. Sci. 2025). Ngoài giao thông: **STAMP ICLR 2025** (cặp adapter–reverter hai phía giữa các agent train độc lập, collaborative perception); PolyInter CVPR 2025; TaCA, MUSCLE (adapter tương thích sau khi nâng cấp mô hình) | Không có vòng điều khiển kín, không có hiệu ứng dự báo tự phá, không có giao thông |
| C6 | Đăng ký trước, NI, crossed bootstrap qua seed hai quần thể | COMPONENT | Owen & Eckles 2012 (bootstrap mảng nhiều chiều); **Li & Wellman IJCAI 2024** (bootstrap meta-game qua seed); Colas 2018 | Không có trong giao thông/eco-driving |
| C7 | Mô hình nhỏ chính xác của phản hồi dự báo qua hàng đợi | BACKGROUND | Bottom 2000; Wu & Amin 2019 (information design, chọn tuyến); JASSS 2004; Dong et al. Physica A 2009 | Chỉ chọn tuyến; không có đèn hay hàng đợi tại nút |

## 3. Work mới phải trích, theo thứ tự

1. **Genser et al. 2024**: trích đúng đoạn Discussion (arXiv 2208.11344v1). Nguyên văn: "when motion planning algorithms consider the
   predictions of the T2G … the timestamp of an LD detection will also change. Consequently, the proposed models … (offline learning) can
   not dynamically adapt to the new system behavior."
2. **Erdmann, "Combining Adaptive Junction Control with Simultaneous GLOSA", WiVeC 2013 (DLR)**: mâu thuẫn giữa GLOSA và đèn adaptive,
   giải bằng cách thiết kế chung (AGLOSA).
3. **RobustLight (Li et al., ICML 2025)** và **MDRC (arXiv 2609.27528, 09/2026)**: module đầu vào cắm trước đèn RL mà không thay nền tảng
   điều khiển.
4. **Siemens EP3594920A1 (2018/2020)**: tín hiệu detector ảo trước controller không đổi, phục vụ GLOSA/T2G.
5. **STAMP (ICLR 2025)**: adapter hai phía giữa các agent train độc lập. Đây là tiền lệ gần nhất cho chữ "two-sided" ở mức ML.
6. **Eteifa, luận án VT 2024** và/hoặc **TTS US10008113B2**: dự báo lai (logic xác định + thống kê/học).
7. **Du, ShangGuan, Chai, Transp. Saf. Environ. 2022 (AD-RLTSC)**: đèn RL quyết định trước nửa chu kỳ rồi phát đếm ngược cho CAV.
   Cùng dòng "đèn học dễ đoán" với Gu 2025 và FoRL.
8. **Ming et al., ITSC 2025**: eco-driving gây blockage/spillover tại nút.
9. Paine 2025 (luận án Southampton): đã biết từ sáng; vẫn chưa đọc được full text. **Bạn nên tự tải bản PDF** để kiểm tra RL controller
   được train cùng GLOSA hay không.
10. Tùy chọn: Sim2Signal 2026; TaCA hoặc MUSCLE; Li & Wellman 2024; Owen & Eckles 2012; Majstorovic 2025; Wu & Amin 2019;
    Performative Time-Series Forecasting (arXiv 2310.06077).

## 4. Sửa chữ trong paper (ĐÃ áp dụng 21:05, ledger C-170; câu về huấn luyện đã chỉnh cho đúng Algorithm alg:cal)

- **Mục SPaT Prediction**, sau câu trích genser2024: "They note that once vehicles plan their speed with these predictions, detector
  timestamps change and an offline-trained predictor cannot adapt, and they suggest online or meta-learning [genser2024]. Our
  forecaster is trained on logs collected with the forecast published, one realization of that suggestion, and we measure the shift
  for a learned signal."
- **The Gap**, thay câu "what is new here is their instance at the signal–eco-driving interface": "At the signal–speed-advice interface
  the effect was anticipated qualitatively for actuated control [genser2024], and the tension between GLOSA and adaptive control was
  noted early [erdmann2013]; what we add is its measurement for a learned, halting-based signal and a repair that retrains neither
  side."
- **Mục DC-Ada / input adapters**: "Input-side modules that restore a frozen signal policy's observations exist for sensor corruption
  [robustlight2025, mdrc2026], and industry places virtual detector signals in front of an unchanged controller to stabilise GLOSA
  [siemens2020]. Ours corrects a shift caused by the partner population, with a two-parameter physical count."
- **Two-sided**: "Two-sided adapters between independently trained agents exist in collaborative perception [stamp2025]; ours act inside
  a closed control loop in which each side's output changes the other's input."

## 5. Thực tiễn và venue (từ bước đọc nguồn của deep-research; mỗi điểm 1 nguồn, chưa qua 3 phiếu)

- **Độ trễ SPaT:** thử thực địa FHWA ở Virginia đo cellular 4G/LTE: trung vị 36 ms, tối đa 68 ms. DSRC khoảng 1 ms.
  - Audit sáng ghi "khoảng 1 s" (UNVERIFIED), giờ có số đo ngược lại.
  - Phép thử 1 s trong paper vì vậy là trường hợp bi quan. Profile DRIVE Sweden yêu cầu độ trễ ≤ 1 s, đó là chặn trên chứ không phải
    trễ điển hình.
- **Profile DRIVE Sweden** bắt buộc likelyTime và confidence (trong SAE J2735 hai trường này là tùy chọn). Đây là lập luận cho đầu ra
  quantile.
- **SUMO:**
  - HBEFA4 là mặc định từ 1.23.0, trong khi trang Emissions vẫn ghi HBEFA3. Khớp với phép kiểm runtime của ta.
  - Gói PHEMlight5 công khai chỉ có 2 lớp Euro-4.
  - Một claim cần tự kiểm: "mọi mô hình HBEFA/PHEMlight coi xe coasting là 0 nhiên liệu".
- **Krauss/IDM/Wiedemann:** cho phát thải khác nhau rõ dù vĩ mô gần nhau; điểm tối ưu thay đổi theo mô hình lái. Ủng hộ việc ta báo
  cáo kết quả IDM.
- **Elsevier, chính sách AI cập nhật 18/08/2026:**
  - Phải nộp riêng một bản khai AI.
  - Nếu AI góp vào thiết kế, phương pháp hay phân tích thì phải mô tả lại trong phần Methods.
- **Venue:**
  - ITSC 2027: hạn 01/03/2027, mở nộp 01/12/2026.
  - T-ITS: 10 trang, tối đa +6 trang, phí 175 USD mỗi trang vượt.
  - HONEST-CAV đã được nhận ở IEEE IV 2026.
- **Triển khai:**
  - Google Green Light không chạy vòng kín (chỉ khuyến nghị chỉnh pha, city tự áp dụng).
  - KI4LSA đã chạy đèn RL thật ở Lemgo từ 2020 đến 08/2022 (white paper).

## 6. Còn hở

- Các work mới ở mục 3 mới được đọc một lượt. Nếu muốn mức 3 phiếu: khoảng 10 work × 3 agent. Nên chạy ngay sau khi giới hạn reset,
  không chạy song song với việc khác.
- Full text của Paine 2025, Ming ITSC 2025 và Han TR-C 2026.
- Tài liệu tiếng Trung: chỉ có metadata.
