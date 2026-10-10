# Poster TSI: bản dịch tiếng Việt và kịch bản 2 phút (06/10/2026)

## Phần 1. Bản dịch poster

**Nâng cấp theo giai đoạn của hai quần thể học máy**
**Giao diện hai phía khôi phục lợi ích của đội xe học máy khi đèn tín hiệu được nâng cấp**
Vu Phan An Nguyen, Zhengping Jay Luo, Khoa Khoa học Máy tính & Toán, Đại học Rider
*Nghiên cứu được tài trợ bởi Quỹ Khoa học Quốc gia Hoa Kỳ (NSF), Award No. 2551962. Mọi quan điểm, phát hiện, kết luận hay khuyến nghị trong tài liệu là của tác giả và không nhất thiết phản ánh quan điểm của NSF.*

### I. Giới thiệu

**Hình 1.** Việc nâng cấp xóa mất lợi ích của đội xe học máy. So với tài xế nền của chính nó, đội xe tiết kiệm nhiên liệu dưới đèn chu kỳ cố định (xanh dương). Dưới đèn học máy mà không có thông tin pha, đội xe trở về đúng tài xế nền (xám, bằng 0 theo định nghĩa). Nếu vẫn phát lịch pha cũ làm SPaT, đội xe tốn thêm cả nhiên liệu lẫn thời gian (cam).

- Đèn tín hiệu và đội xe kết nối đều đang trở thành các policy học máy. Chúng thuộc các chủ sở hữu khác nhau và được nâng cấp theo lịch khác nhau. Một đội xe được huấn luyện dưới đèn chu kỳ cố định đọc thông tin pha và thời gian đèn được phát (SPaT) như một kế hoạch. Còn đèn học máy thì quyết định lại sau mỗi vài giây, nên kế hoạch đó biến mất.
- Trong SUMO, trên lưới 16 nút đèn, một đội xe lái tiết kiệm (eco-driving) huấn luyện bằng PPO tiết kiệm 6.5% nhiên liệu so với tài xế nền dưới đèn cố định. Khoản tiết kiệm này mất hẳn khi đèn chuyển sang học máy (Hình 1).
  - Bỏ thông tin thời gian thì đội xe quay về tài xế nền.
  - Phát dự báo của đèn học máy thì chính các xe của đội bị tốn thời gian.
  - Bắt đèn cam kết lịch, đứng ngoài, hay chạy theo lịch chia pha dự đoán được đều không đạt giới hạn.
- Đầu vào của đội xe không nhất thiết để lộ vấn đề. Trong một ví dụ nhỏ, chứng minh bằng tính chính xác trên mọi trường hợp, việc nâng cấp giữ nguyên phân phối những gì đội xe quan sát, trong khi luật đã học của nó trở nên tệ gấp mười lần luật tốt nhất. Cách chữa thường dùng là huấn luyện lại, nhưng hai bên sở hữu hiếm khi cùng huấn luyện lại. Vì vậy chúng tôi giữ nguyên (đóng băng) cả hai policy và chỉ thay đổi hai giao diện giữa chúng: điều được báo cho đội xe, và điều đèn đếm.

### Công trình liên quan

- Các nghiên cứu trước chỉ sửa một phía.
  - Dự báo SPaT cho đèn thích ứng [1, 2] và GLOSA ở đèn thích ứng cao [3] cải thiện dự báo.
  - Eco-driving khi thời gian đèn không chắc chắn hoặc theo cảm biến [4, 5] thay đổi phía xe.
  - Điều khiển kết hợp, và FoRL [6] (huấn luyện đèn dự báo và giữ đúng hành động của chính nó), huấn luyện lại một policy.
  - DC-Ada [7] điều chỉnh đầu vào của một policy đóng băng bằng tìm kiếm chỉ dựa trên phần thưởng.
- Lỗi ở đây là một dự báo tự phá. Đây là bài toán nhất quán của dẫn đường dự đoán trước [8] và của dự báo tác động (performative prediction) [9]. Dạng mới của nó, ở giao diện giữa đèn và eco-driving, là phản ứng của đội xe với dự báo đi qua chính đầu vào của đèn (Hình 2).

### II. Phương pháp

**Hình 2.** Vòng kín và hai giao diện mà TSI thay đổi (xanh). Khi thời gian đèn được công bố, xe trong đội lướt chậm vào giao lộ. Đèn đếm xe dừng thì không đếm những xe này nữa, nên giữ xanh lâu hơn, và đích của chính dự báo bị dịch đi (cam).

- **Thử nghiệm.**
  - Lưới 16 đèn (grid4), mỗi chiều hai làn.
  - Một policy đèn double-DQN dùng chung cho mọi nút, giữ hoặc chuyển pha dựa trên số xe đang dừng (quyết định mỗi 5 s, vàng 3 s).
  - Đội xe eco-approach huấn luyện bằng PPO, dùng SPaT; một nửa số xe là xe của đội.
  - Mỗi lần xác nhận gồm 5 đèn × 4 đội xe × 20 seed giao thông mới.
- Nghiên cứu đi qua bốn giai đoạn, luật quyết định của mỗi giai đoạn được chốt trước khi xác nhận:
  - M1: có một đội xe đáng bảo vệ.
  - M2: nâng cấp xóa lợi ích của nó, đo bằng hiệu của hiệu (difference in differences) so với tài xế nền σ*.
  - M3: sửa chỉ qua hai giao diện.
  - M4: chuyển sang giao thông, policy và mạng mới.
- **Phía đội xe.** Lịch pha cũ được thay bằng một bộ cung cấp lai:
  - chính xác khi thời gian đã được xác định (pha vàng mà pha xanh kế tiếp phục vụ làn đó);
  - ngoài ra, một bộ dự báo quantile theo trạng thái, huấn luyện trên 8 episode ghi log của chính đèn đang triển khai, với hàm mất mát pinball có trọng số theo tần suất truy vấn.
- **Phía đèn.** Cho đèn đóng băng đếm cả xe đang lướt: một bộ đếm theo dải tốc độ đặt trước đầu vào đếm-xe-dừng của đèn. A = B = 0 là đèn gốc; (A, B) được chỉnh cho từng đèn. Hiệu chỉnh tốn 52 episode mô phỏng mỗi đèn, và không có bước gradient nào cho cả hai policy.
- **Luật quyết định.** Một cách sửa chỉ đạt khi:
  - nhiên liệu của đội xe giảm;
  - mọi time loss (toàn thành phố, đội xe, xe người) tăng không quá +0.5 s/xe, tính ở cận trên một phía của bootstrap chéo theo seed đèn, seed đội xe và seed giao thông;
  - không tăng số xe bị teleport hay chuyến chưa hoàn thành.

### II. Phương pháp (tiếp)

- **Vì sao cần cả hai phía.** Trong một mô hình hàng đợi theo ngưỡng, một tỷ lệ ρ của dòng xe lướt chậm, và đầu vào của đèn đếm mỗi xe lướt với trọng số A. Khi đó dự báo học khi chưa có đội xe sẽ sai một lượng như phương trình.
- Trong mô hình này:
  - Đếm xe lướt thấp hơn xe dừng (A < 1) làm đèn phục vụ trễ hơn dự báo, và trễ càng nhiều khi đội xe càng lớn.
  - Đếm ngang nhau (A = 1) xóa độ lệch.
  - Với n xe, bộ đếm-xe-dừng bỏ sót nhu cầu với xác suất ít nhất pⁿ.
  - Trong mô hình một xe, sửa riêng một phía chắc chắn thất bại (đã chứng minh), sửa cả hai phía đạt tối ưu.
  - Chứng minh: bằng đại số (mô hình hàng đợi) và xét hết mọi trường hợp (mô hình một xe), tất cả được máy tính kiểm lại.
- Thời gian xanh đo được thay đổi đúng hướng mô hình gợi ý, dù các đèn học máy không phải luật ngưỡng:
  - dài hơn khi có dịch vụ dự báo với đèn đếm-xe-dừng (grid4 15.0 → 17.1 s; spider 18.9 → 28.7 s);
  - không đổi với MaxPressure (18.1 → 18.0 s);
  - trở về 15.0 s dưới TSI trên grid4.

### III. Kết quả

**Hình 3.** TSI so với phương án dự phòng không có SPaT trong mọi phép thử đã đăng ký (khoảng tin cậy 95%; kết luận ở mức ý nghĩa của từng phép thử).

- Huấn luyện lại đội xe thay vì dùng TSI: không phát hiện khác biệt nhiên liệu, và time loss cao hơn TSI; chưa chứng minh được không-kém-hơn về nhiên liệu ở biên 0.5 điểm phần trăm.
- **Khoảng ba phần năm lợi ích được khôi phục.** Trong lần xác nhận đã đăng ký, TSI giảm nhiên liệu của đội xe 3.85% (KTC 95%: 3.26–4.43), mọi time loss nằm trong giới hạn. Riêng dịch vụ dự báo, hay riêng adapter, đều thất bại trong mọi phép bóc tách.
- **Kết quả lặp lại được.**
  - Trên ba panel giao thông khác: −3.70%, −3.85%, −3.86%.
  - Trên hai bộ đèn và đội xe huấn luyện lại độc lập, hiệu chỉnh từ đầu: −2.61%, −2.97%.
  - Một cấu hình adapter duy nhất (A, B) = (1, 0.5), chốt từ trước, cũng đạt mọi giới hạn trên các policy grid4 chưa từng thấy (−2.88%).
- **Các phương pháp đã công bố, chuyển sang bài toán này, đều không đạt giới hạn trên cùng giao thông.**
  - DC-Ada, cùng ngân sách mô phỏng, tiết kiệm nhiên liệu tương tự (−3.45%) nhưng tăng time loss của đội xe 2.87 s/xe.
  - Bản chuyển FoRL của chúng tôi (huấn luyện lại đèn) cũng thất bại: ngay cả ở đúng thang phần thưởng của tác giả, dự báo của nó tiết kiệm 0.70% nhiên liệu nhưng tăng 0.52 s/xe.

### IV. Thảo luận

**Hình 4.** Cơ chế:
- (A) khi có dịch vụ dự báo, đèn học máy giữ xanh lâu hơn;
- (B) phần thời gian tốn thêm của đội xe tăng theo độ kéo dài đó;
- (C) trên lịch đèn phát lại, thông tin pha chính xác tiết kiệm cả nhiên liệu lẫn thời gian.

- **Một dự đoán đưa ra trước khi chạy đã đúng.** MaxPressure đếm xe ở mọi tốc độ, nên mô hình nói chỉ cần dự báo là đủ. Đã đăng ký trước: riêng dịch vụ phía đội xe đạt mọi giới hạn (−2.68%), và thời gian xanh không bị kéo dài.
- **Khả năng chuyển giao có điều kiện.**
  - Mạng rand3 đạt khi mở rộng phạm vi adapter (−2.17%).
  - Spider một làn thất bại cả bốn lần đã đăng ký. Bộ dự báo huấn luyện lại, thông tin pha chính xác khi phát lại, hay nhả quyền cho xe đang dẫn một xe người phía sau đều không xóa được phần thời gian tốn thêm. Phần này nằm ở lịch đèn vòng kín.
  - Spider dựng lại hai làn, với lịch pha mới và các policy huấn luyện lại, thì đạt (−1.49%).
- **Độ bền.**
  - Vẫn trong giới hạn khi chỉ phát hiện 80% xe, nhiễu tốc độ 1 m/s, và mất 20% tin nhắn.
  - Câu trả lời cũ ít nhất 1 giây làm khoản tiết kiệm giảm còn 0.74%.

### Giới hạn

- Chỉ là mô phỏng, trên ba mạng tổng hợp. Khoản tiết kiệm đúng với mô hình HBEFA4, nhưng thành tăng 1.76% nhiên liệu với PHEMlight5 trên cùng quỹ đạo xe. Thiết kế đóng băng không trụ được khi đổi sang tài xế IDM.
- Còn để ngỏ:
  - đặc tính nào của lịch đèn vòng kín gây tốn thời gian trên spider một làn;
  - mỗi đèn triển khai cần log riêng của nó;
  - mô hình hàng đợi là một luật ngưỡng cách điệu, không phải các đèn học máy.

### V. Kết luận

- Khi một quần thể học máy được nâng cấp, một cặp đang chạy tốt có thể hỏng dù không policy nào thay đổi. Không giao diện nào sửa được một mình. Cùng nhau, chúng khôi phục khoảng ba phần năm lợi ích của đội xe mà vẫn giữ nguyên cả hai policy, trên grid4 và, có điều kiện, trên các mạng khác.
- Trước khi nâng cấp đèn mà một đội xe học máy đang dựa vào, hãy kiểm tra xem đầu vào của đèn có đếm được cách tiếp cận chậm của đội xe không, và thử trước trên đường một làn.

## Phần 2. Kịch bản 2 phút (khoảng 280 từ tiếng Anh, nói khoảng 140 từ/phút)

| # | English (nói) | Tiếng Việt (để hiểu và tập) | Chỉ vào |
|---|---|---|---|
| 1 | "Cities are starting to run learned traffic signals, and carmakers run learned eco-driving fleets. They have different owners and are upgraded on different schedules." | "Thành phố bắt đầu dùng đèn tín hiệu học máy, còn hãng xe dùng đội xe lái tiết kiệm học máy. Hai bên thuộc chủ khác nhau và nâng cấp theo lịch khác nhau." | Tiêu đề |
| 2 | "Our fleet saves 6.5% fuel under fixed-time signals. Once the signals become learned, that benefit is gone, and publishing a forecast of the new signal even costs the fleet time." | "Đội xe của chúng tôi tiết kiệm 6.5% nhiên liệu dưới đèn cố định. Khi đèn chuyển sang học máy, lợi ích đó mất hẳn, và phát dự báo của đèn mới còn làm đội xe tốn thời gian." | Hình 1 |
| 3 | "Why? It's a loop. Published timing makes cars glide in slowly. The signal counts only stopped cars, so it stops seeing them, holds its green longer, and the forecast defeats itself." | "Vì sao? Đó là một vòng kín. Khi có thông tin pha, xe lướt chậm vào giao lộ. Đèn chỉ đếm xe dừng nên không thấy chúng, giữ xanh lâu hơn, và dự báo tự phá chính nó." | Vòng cam, Hình 2 |
| 4 | "So we freeze both policies and fix the two interfaces: the fleet gets exact timing during yellow and a learned forecast otherwise, and the signal also counts slow cars." | "Nên chúng tôi giữ nguyên cả hai policy và sửa hai giao diện: đội xe nhận thời gian chính xác trong pha vàng và dự báo học được ở lúc khác, còn đèn đếm thêm cả xe chậm." | Hai ô xanh |
| 5 | "A small queue model, which we prove by algebra and check by computer, shows why one side alone can't work: the forecast is only right when gliding cars count like stopped ones." | "Một mô hình hàng đợi nhỏ, chứng minh bằng đại số và kiểm lại bằng máy tính, cho thấy vì sao sửa một phía không đủ: dự báo chỉ đúng khi xe lướt được đếm như xe dừng." | Phương trình queue |
| 6 | "In a pre-registered confirmation, this recovers about three-fifths of the lost benefit, 3.85% fuel, with no extra time loss. Each half alone fails. It replicates on new traffic and newly trained policies, and beats ported DC-Ada and FoRL on the time limits." | "Trong lần xác nhận đăng ký trước, cách này lấy lại khoảng ba phần năm lợi ích đã mất, 3.85% nhiên liệu, không tốn thêm thời gian. Mỗi nửa riêng lẻ đều thất bại. Kết quả lặp lại trên giao thông mới, policy huấn luyện mới, và vượt DC-Ada lẫn FoRL về giới hạn thời gian." | Hình 3 + cột 3 |
| 7 | "Limits: it's simulation only, the fuel result depends on the emission model, and it fails on a one-lane network." | "Giới hạn: chỉ là mô phỏng, kết quả nhiên liệu phụ thuộc mô hình phát thải, và thất bại trên mạng một làn." | Limitations |
| 8 | "Takeaway: before upgrading signals a learned fleet relies on, check whether the signal can see the fleet's slow approach." | "Thông điệp: trước khi nâng cấp đèn mà một đội xe học máy dựa vào, hãy kiểm tra xem đèn có nhìn thấy cách xe tiếp cận chậm không." | Conclusions |

**Mẹo tập:**
- Mỗi dòng là một hơi nói, khoảng 15 giây.
- Nếu chỉ còn 1 phút, nói dòng 1, 3, 4, 6 và 8.
- Từ khó đọc: *eco-driving* (i-cô), *pre-registered*, *three-fifths* (thri-fíp-thz), *self-defeating*.
