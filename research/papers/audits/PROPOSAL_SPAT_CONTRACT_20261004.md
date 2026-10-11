# Đề xuất (chưa chạy, chờ người dùng quyết): hợp đồng SPaT giữa đèn học và đội xe học

Viết 04/10/2026 06:28 EDT (wake 4), sau khi B6, B6-N và B6-D1 âm. Đây là nhánh mà cây quyết định B6 (Branch N, đoạn cuối) đã chỉ tới: *"đổi mô hình đội xe theo hướng thông tin (SPaT / V2I), như một hướng mới, đăng ký riêng"*.

## Vì sao

| Bằng chứng | Nguồn |
|---|---|
| Không đội xe nào thắng mô hình lái mặc định của SUMO: v1, v2, v3, release, (residual chờ chạy lại). Đội xe chỉ thấy "pha đã kéo dài bao lâu", không thấy "còn bao lâu". | C-17, C-21, C-22 |
| Văn liệu eco-driving bằng RL có lợi thật khi xe NHẬN SPaT: tới −18 % xăng, tốc độ +20 % (Jayawardana & Wu 2022, arXiv 2204.12561). GLOSA với SPaT tốt: 8–32 % xăng. | web | *[ĐÍNH CHÍNH, xem cuối file]*
| GLOSA dựa vào SPaT tệ nhất dưới đèn actuated trong chính repo (Q2b: +128). Văn liệu: SPaT của đèn actuated / adaptive không chắc chắn; sai số ±3.3 s còn giữ khoảng 85 % lợi ích. | C-4; arXiv 2208.13709 |

## Câu hỏi (hai quần thể, nâng cấp so le, đúng mạch E3)

1. Đội xe F học eco-driving với SPaT của đèn fixed-time (SPaT chính xác). **B6 phải đạt trước:** F thắng always-SUMO về xăng và không thua về TL. *[ĐÍNH CHÍNH, xem cuối file]*
2. Thành phố nâng cấp đèn lên đèn học (RL-H). SPaT không còn dự đoán được, nên F suy giảm.
3. **Ba cách sửa, có quyền khác nhau:**
   - **(a) Đèn giả lập hợp đồng cũ:** cam kết thời điểm chuyển pha trước W giây và công bố SPaT đúng. Đây là legacy-view emulation ở phía vật lý; Q5 commitment windows có sẵn. *[ĐÍNH CHÍNH, xem cuối file]*
   - **(b) Đội xe tự bảo vệ:** cổng / guard khi SPaT không đáng tin.
   - **(c) Train lại.**
4. **Đo:** lợi ích nâng cấp của đèn còn lại bao nhiêu khi phải cam kết, so với lợi ích xe giữ được. Đây là frontier "chi phí cam kết ↔ lợi ích partner", đã đăng ký endpoint trước.

## Collision cần đọc sâu trước khi claim

Các khối sau đã có văn liệu:
- dự báo SPaT cho đèn actuated (deep ensemble, PMC11944547);
- quỹ đạo CAV bền với sai số thời gian của đèn (arXiv 2208.13709);
- điều khiển đèn có cam kết cho CAV;
- CoTV (đồng điều khiển).

Phần còn khả năng mới: đội xe ĐÃ HỌC phụ thuộc vào giao diện của một đèn ĐÃ HỌC; nâng cấp so le; đèn mới giả lập giao diện cũ; và frontier chi phí cam kết đo trên cả hai quần thể. Đây là ứng viên, chưa phải claim.

## Kế hoạch tối thiểu nếu được duyệt (khoảng 0.5 ngày máy)

| Bước | Nội dung |
|---|---|
| S0 | Thêm quan sát SPaT cho xe: thời gian còn lại tới lần chuyển pha kế tiếp, `getNextSwitch − t`, chính xác dưới FT. Đây là một trainer mới (v7) trên nền v6 đã làm sạch, train dưới FT. |
| S1 | B6 cho đội xe SPaT dưới FT (screen rồi xác nhận, đúng tiêu chí B6). |
| S2 | Dưới RL-H: (i) SPaT "thô", vô nghĩa với đèn học; (ii) đèn cam kết W ∈ {5, 10, 20} s; (iii) guard phía xe. Đo lợi ích xe và gain của đèn. |
| S3 | Xác nhận trên seed / traffic mới và trên Cologne8. |

Không bắt đầu S0 khi chưa có đồng ý của bạn.

## Kiểm khả thi (08:51): SPaT có thật trong từng loại đèn không?

Probe: seed 100, 1800 s. Ở giây thứ 5 của mỗi pha, ghi thời điểm chuyển mà SUMO công bố (`getNextSwitch`), rồi so với lúc pha thật sự đổi.

| Đèn | Số pha | Sai lệch \|thực − công bố\| trung bình | Ghi chú |
|---|---|---|---|
| FT (static) | 640 | 1.0 s | Đúng bằng độ lệch 1 s do thời điểm quan sát, tức SPaT **chính xác** | *[ĐÍNH CHÍNH, xem cuối file]*
| ACT (actuated) | 663 | 2.35 s | Gap-out làm chuyển sớm |
| RL-H (đèn học) | 1518 | ≈ 1e5 s | LightRL giữ pha bằng duration 1e5, nên **không có SPaT nào** nếu đèn không cam kết | *[ĐÍNH CHÍNH, xem cuối file]*

Tiền đề của đề xuất được xác nhận: nâng cấp từ FT sang đèn học xoá giao diện SPaT, trừ khi đèn mới cam kết thời điểm chuyển (giả lập hợp đồng cũ). *[ĐÍNH CHÍNH, xem cuối file]*

## Đọc sâu Jayawardana & Wu 2022 (arXiv 2204.12561; 08:52), để thiết kế S0 nếu được duyệt

| Khía cạnh | Thiết lập của họ |
|---|---|
| Quan sát | tốc độ và vị trí xe, pha đèn (one-hot), tốc độ / vị trí xe trước và xe sau, **time-to-green (SPaT)**; chuẩn hoá min-max |
| Reward | nhiều thành phần: phạt dừng ở đầu đoạn, thưởng tốc độ, phạt xăng mũ |
| Thuật toán | TRPO, CTDE; gia tốc liên tục; bước 0.5 s; 600 bước |
| Đèn | **fixed-time** 30 s xanh / 4 s vàng; không bàn đèn khó dự đoán |
| Fuel | mô hình VT-CPFM |
| Kết quả | −17.8 % xăng, −25.4 % CO₂, +20 % tốc độ so với IDM ở 100 % CAV; 25 % CAV đạt ≥ 50 % lợi ích |

**Hệ quả cho S0:**
- Thêm time-to-switch, pha hiện tại và xe sau vào quan sát.
- Hành động mịn hơn hoặc liên tục.
- Ngân sách lớn: B6-R cho thấy ×4 đã thay đổi kết quả.
- Đánh giá với cả ρ = 0.5 lẫn ρ = 1.0. Lợi ích của họ đo ở 100 % CAV, còn panel của mình ở ρ = 0.5.

**Khoảng trống:** họ không xét đèn khó dự đoán hay được nâng cấp. Đó đúng là phần đề xuất này nhắm tới.

## Hệ quả của B6-Z cho đề xuất (ghi 09:04, ledger C-25)

Đội xe ra lệnh tốc độ sẽ xoá luôn imperfection σ = 0.5 của mô hình Krauss trên những xe nó lái. Smoke cho thấy chỉ riêng việc đặt σ = 0, không học gì, đã nhanh hơn always-SUMO khoảng 4 s/veh (một seed, chưa phải bằng chứng). Vì vậy, nếu đề xuất được duyệt:

- **S1 phải thắng Z-sig0** (SUMO, σ = 0), không chỉ thắng always-SUMO. Đây là comparator "tài xế hoàn hảo không có thông tin". *[ĐÍNH CHÍNH, xem cuối file]*
- **Lợi ích của SPaT phải được đo so với cùng lớp chính sách khi không có SPaT.** Hiệu số đó mới là thông tin; σ = 0 thì không phải.
- **Lớp hành động phải chứa được SUMO.** Release đã đạt (Z-1). ACC và fine không launch kịp 2.6 m/s². Residual với δ = 0 thì kẹt (C-25).

## Phương án phụ (chưa làm, chờ bạn): ghi chú phương pháp về các bẫy khi đánh giá đội xe học trong SUMO (09:14)

Bốn bẫy có bằng chứng trong ledger:

| Bẫy | Ledger |
|---|---|
| reward thưởng lệnh thay vì vật lý (v1) | C-17 |
| sentinel `INVALID_DOUBLE_VALUE` của xe đang teleport lọt vào reward | C-22 |
| `getSpeedWithoutTraCI` bị chặn trên bởi `setSpeed`, nên lớp residual không chứa SUMO | C-25 / C-27 |
| comparator σ = 0: lợi thế thời gian của đội xe học nhỏ hơn việc chỉ bỏ imperfection | C-27 |

**Collision sơ bộ:**
- Makantasis et al. (arXiv 1907.05246) đánh giá với σ = 0 và σ = 0.5 cho xe người, nhưng không dùng σ = 0 làm comparator cho chính xe RL.
- arXiv 2311.08429 so sánh mức tương đương phân phối giữa các simulator.

**Đánh giá:** mới ở mức workshop, có ích thực hành. Đây không phải đích của chương trình hai quần thể. Chỉ làm nếu bạn muốn.

## Cập nhật sau B6-S (09:17, C-28)

Bar cho S1 nâng lên: đội xe SPaT phải **vượt họ σ** theo định nghĩa S-2, tức là với MỌI σ, nó phải tốt hơn về TL hoặc về xăng với cận một phía 95 %. Chỉ thắng always-SUMO là không đủ. σ = 0.3 đã cho −2.5 s/veh và −2.2 % xăng mà không cần học hay thông tin gì.

Một biến thể rẻ hơn của đề xuất: dùng **đội xe không học có SPaT**, ví dụ GLOSA kinh điển trên nền σ tốt nhất, làm quần thể xe trong nghiên cứu nâng cấp đèn. Như vậy câu hỏi "nâng cấp đèn phá giao diện SPaT" tách khỏi câu hỏi "học được đội xe tốt".

## Đính chính theo audit `CITY_B6_FINAL_AND_SPAT_AUDIT_20261004` §3 (12:05; không chạy gì)

Tôi đồng ý cả bảy điểm.

| # | Câu cũ | Đúng là |
|---|---|---|
| 1 | "RL eco-driving có lợi thật khi xe NHẬN SPaT" (Jayawardana–Wu) | Bài đó cho thấy **một cấu hình** RL có SPaT có lợi: TRPO, gia tốc liên tục, có xe trước / sau, đèn fixed-time, VT-CPFM. Nó **không** chứng minh chỉ có SPaT mới thắng. Muốn đo SPaT đóng góp bao nhiêu phải so **cùng recipe có / không SPaT**. |
| 2 | "`getNextSwitch − t`" là SPaT; "FT lệch 1.0 s, tức SPaT chính xác" | `getNextSwitch` là thời điểm chuyển pha kế tiếp *giả định* (SUMO docs), không phải time-to-green của movement xe sẽ đi: pha vàng, hoặc pha xanh của hướng khác, là phản ví dụ. Lệch 1.0 s dưới FT **phù hợp** với một offset 1 s, nhưng chưa được kiểm theo từng trace. SPaT đúng phải tính theo movement, từ link index của xe và kế hoạch pha, kèm timestamp và cờ hợp lệ; dưới FT phải kiểm bằng trace. |
| 3 | "RL-H ≈ 1e5: không có SPaT nào nếu đèn không cam kết" | 1e5 là **artifact của cách cài đặt** (LightRL đặt duration 1e5 để giữ pha). Nó chỉ cho thấy API raw không phải forecast. Nó **không** chứng minh đèn học không dự báo được. Không đưa 1e5 cho xe rồi "sửa" nó, vì như thế là tạo hazard bằng interface lỗi. Đối chứng phải là một **forecast causal hợp lệ** (kèm cờ unavailable / uncertainty) và một baseline robust dùng cùng thông tin. |
| 4 | Collision list | Adaptive-SPaT đã có **prior art trực tiếp**: báo cáo *Connected Eco-Driving Technologies for Adaptive Traffic Signal Control* (USDOT, min / max / likely time + confidence, NYC / Arcadia). Đây là đối chứng bắt buộc. |
| 5 | Phần còn mới | Eco-driving chịu sai số SPaT đã có (Shafik et al., arXiv 2208.13709), nên không claim mới ở "xe bền với thời điểm đèn đổi". |
| 6 | "(a) Đèn giả lập hợp đồng cũ: legacy-view emulation ở phía vật lý" | **Sai.** E3 dựng lại một view từ packet. Cam kết pha thì đổi hành động và dynamics thật. Chỉ kế thừa được **thiết kế so sánh quyền sửa / chi phí**, không kế thừa định lý hay đảm bảo return. |
| 7 | "W ∈ {5, 10, 20} s" | Q5 (C-6) cho thấy commitment đắt. Ở demand không bão hoà, COMMIT(0) đẩy delay từ 13.8 lên 22.1 s/veh, và không cửa sổ nào vừa giữ chi phí đèn ≤ 5 % vừa giữ phần lớn lợi ích của xe. Phải đối chiếu semantics cửa sổ của Q5 trước khi đồng nhất với "cam kết trước W giây". Không mặc định fixed-W là phương pháp. |

**Đề xuất cũ S0–S3 được thay** bằng pilot có ablation thông tin (`research/city_sim/PROTOCOL_CITY_SPAT_PILOT_20261004.md`, bản DRAFT, chưa chạy). Ứng viên phương pháp, chỉ là giả thuyết: **cam kết dự báo vừa đủ cho quyết định của receiver** (receiver-aware commitment). Nó chỉ được kiểm nếu Bước 3 cho thấy regression thật, và phải so với fixed-W commitment và forecast cùng chi phí.
