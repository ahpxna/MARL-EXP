# Kiểm tra kết quả seeds 8201–8203 — 07/09/2026

Chỉ đọc artifact và tính lại summary từ raw records; không chạy thêm experiment, training hoặc Lean. Phân tích này dùng ba thư mục confirm_20260907_030500, confirm_20260907_030529 và confirm_20260907_030535 trong /Users/phanan/cig-amf-main/research. Các lượt sửa lỗi seed 7101 ở outputs không được trộn vào đợt này.

## MASTER: lợi ích lặp lại ở cả ba seed

Tại tolerance 0.1, mỗi seed có 450 world/budget instances với exact regret sẵn có. Mỗi instance được dùng lại ở chín tolerance, vì vậy không tính 4.050 dòng/seed là 4.050 world độc lập.

| Seed | Gamma-box | Gamma-op | Chênh lệch |
|---|---:|---:|---:|
| 8201 | 281/450 = 62.44% | 245/450 = 54.44% | +8.00 điểm % |
| 8202 | 286/450 = 63.56% | 253/450 = 56.22% | +7.33 điểm % |
| 8203 | 295/450 = 65.56% | 255/450 = 56.67% | +8.89 điểm % |
| Tổng | 862/1350 = 63.85% | 753/1350 = 55.78% | +8.07 điểm % |

Tính lại trực tiếp từ certificate và regret xác nhận summary. Cả hai bound cover regret trên toàn bộ 1.350 instance tại tolerance này, không có false-safe quan sát được. Gamma-box không lớn hơn Gamma-op.

Đoạn có thể đưa vào báo cáo: “Trong benchmark hữu hạn trên ba seed 8201–8203, với 450 instance/seed và tolerance 0.1, Gamma-box chứng nhận 63.85% instance, so với 55.78% của Gamma-op. Mức tăng theo seed là 7.33–8.89 điểm phần trăm. Không quan sát false-safe trên tập đánh giá này.”

Giới hạn: runner dựng error = abs(noise)+1e-12 từ truth, nên đây là bằng chứng utility khi interval đã chứa truth; không phải kiểm chứng coverage của estimator học từ dữ liệu. Artifact vẫn mang DEVELOPMENT_EMPIRICAL. Chưa có cơ sở kết luận tiết kiệm runtime vì phép tính certificate hiện bao gồm cả hai Gamma và geometry có exact enumeration.

Hành động: cập nhật phần utility bằng bảng ba seed; nếu muốn claim statistical validity hoặc runtime advantage thì đó là hai nghĩa vụ riêng, không được suy từ tỷ lệ certify.

## Structural: hai menu đủ trong mẫu; bộ test khá dễ

| Seed | Mean worst-budget regret, exact/greedy, K=1 | Exact/greedy, K=2 | Deep, K=2 |
|---|---:|---:|---:|
| 8201 | 0.041667 | 0 | 1.333333 |
| 8202 | 0.041667 | 0 | 1.333333 |
| 8203 | 0 | 0 | 1.541667 |

Exact và greedy đều có worst-budget regret bằng 0 trên 36/36 test world từ K=2 đến K=4. Tuy nhiên 34/36 world đã có regret 0 với K=1; trong hai world còn lại worst-budget regret là 0.5. Không diễn giải hai menu là giới hạn phổ quát của lớp bài toán.

Deep kém exact/greedy theo mean worst-budget regret ở cả ba seed, tại mọi K đã thử. Đây là kết quả của cấu hình 32 train world, 12 test world/seed, 120 epochs; không phải chứng minh deep learning luôn kém greedy. Các regret và số trung bình đã được đối chiếu từ raw per-budget records.

Đoạn báo cáo: “Trên 36 test world thuộc ba seed, exact và greedy đạt zero worst-budget regret với hai menu. Một menu đã đủ ở 34/36 world. KPrefixNet trong cấu hình huấn luyện đã thử có regret lớn hơn cả hai baseline trên cả ba seed.”

Hành động: có thể viết kết quả hiện tại. Nếu muốn làm rõ giá trị của nhiều menu, bổ sung family staircase có prefix-cover dimension biết trước và lớn hơn 2; ghi rõ đó là stress test được dựng, không trộn với mẫu random hiện tại. Chưa cần tăng epochs để tìm một kết quả thuận lợi cho mạng.

## Functional: sửa starvation có tác dụng; chưa có winner

Đúng protocol functional_variance_stopping_v2_balanced_batches, 60 instance/variant.

| Variant | Certificate emitted | Min cell count trên toàn bộ lượt | False-safe quan sát |
|---|---:|---:|---:|
| uniform | 8/60 = 13.33% | 186 | 0 |
| C_split | 9/60 = 15.00% | 53 | 0 |
| C_pilot | 11/60 = 18.33% | 95 | 0 |
| C_shrink | 11/60 = 18.33% | 95 | 0 |
| C_anytime | 8/60 = 13.33% | 2 | 0 |
| C_known_sigma (oracle) | 26/60 = 43.33% | 2 | 0 |

Uniform counts cân bằng: chênh lệch lớn nhất/nhỏ nhất trong mỗi instance không quá 1. Không còn starvation kiểu reset batch ở uniform và các pilot/split. Tất cả median censored N_certificate đều bằng 16.385, tức sentinel max_n+1; không phải đã certify sau 16.385 mẫu. Status đúng là NO_MEDIAN_IDENTIFIED_CENSORING. Không dùng chênh lệch trước/sau giữa seed 7101 và 8201 như một so sánh matched.

Hai vấn đề còn lại:

1. C_anytime có 36/60 lượt còn ít nhất một ô ở count=2, interval width trung bình khoảng 14.501,68. Cần kiểm tra khả năng tiếp tục khám phá của driver-selection; không mặc định đây là lỗi reset batch cũ. Hai mẫu có thể vẫn chấp nhận được cho ô không còn liên quan, nhưng ở đây interval rất rộng và mức censor cao khiến starvation còn là vấn đề cần giải quyết.
2. C_pilot và C_shrink có toàn bộ records giống nhau trên 60/60 instance, trừ tên variant. Trong code, shrink biến đổi sigma bằng một hàm đơn điệu chung; allocator chỉ sort theo scale rồi cấp mẫu vòng tròn, nên nó không dùng độ lớn của scale. Ablation shrink hiện không tạo ra chính sách khác. Nếu claim muốn đánh giá variance-weighted allocation, cần dùng trọng số thực; nếu không, gộp hai nhãn.

Hành động: xử lý hai điểm trên và lưu true Top-K gap, min counts, terminal interval widths theo instance để phân biệt thiếu budget, gap khó và driver starvation. Sau đó mới quyết định cần thêm budget hay thay confidence construction. Không công bố “pilot thắng” từ 11 so với 8 certificate.

## Query: gate đã mở, scientific signal vẫn bằng 0

- status OK; 8/8 executable states, tám state_hash khác nhau.
- scientific_transfer_status EVALUABLE_DEGENERATE.
- 48/48 state-query targets có utility oscillation 0.
- 336 method-query-state cells: 0 regret-evaluable, 0 ranking-evaluable.
- Matched budget 32 chặn thêm 288/336 cell; ngay cả full-information cũng không có cell evaluable nên budget không phải nguyên nhân duy nhất.
- AttentionWeights, CausalContextAttribution, CommunicationDelay, MessageDeletion và VoI vẫn thiếu provider.

Gate repair đã được xác nhận về mặt thực thi. Không gọi regret 0 trên target hằng là thành công transfer, và không đọc benchmark_readiness mang chữ READY như kết luận scientific readiness.

Hành động: định nghĩa target và state distribution có ý nghĩa trước. Runner đang đo reward một bước Q_one_step sau warmup ba bước. Nếu muốn continuation value, phải thay estimand, protocol và kiểm tra fixed continuation; tăng warmup không tự biến one-step reward thành continuation return. Nếu giữ one-step estimand, cần state distribution đã định trước với cơ hội tác động lên reward, đồng thời báo cáo tỷ lệ degenerate trên toàn bộ mẫu thay vì chỉ giữ state có tín hiệu. Không cần thêm seed theo cấu hình hiện tại.

## Ghi nhận Lean, không rebuild

LeanD6SharpnessM6V1.olean (03:25) mới hơn source (03:19); AxiomAuditD6SharpnessM6V1.olean có timestamp 03:26. Đây là chứng cứ artifact compile có tồn tại.

Scope cần giữ chính xác: module này chứng minh công thức residual của họ nguyên và các quan hệ giữa twoD và deltaBox. deltaBox s được định nghĩa là 2*s+2; trong file hiện tại chưa có theorem nối nó với mixedDifference của Vb, còn strict_topC_margin_two là đẳng thức/bất đẳng thức số học, chưa là StrictTopC của chain. Tên six_optimal_at_m6 không tự thay thế semantic bridge cho toàn họ. Phản ví dụ m-1 đã đóng trong module binary bridge trước đó; ghi nhận này không mở lại phản ví dụ ấy.

## Dữ liệu kiểm tra

CONFIRM_RESULTS_20260907.json lưu số đếm tính lại, đường dẫn các input và các kiểm tra nhất quán. Toàn bộ kiểm tra raw/summary đã pass. Không chạy thêm experiment trong lượt kiểm tra này.
