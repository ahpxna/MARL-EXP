# Đánh giá khả năng công bố: paper TSI hai quần thể (06/10/2026, 05:5x)

**Nguồn.**
- 4 agent (A collision, B chuẩn reviewer, C thực tiễn, D venue) cùng hai đợt search của agent chính.
- Agent chính tự kiểm lại các phát hiện có tác động lớn: MATES, EP3985636, Paine 2025, ITSC 2027, Maadi 2022, lớp phát thải mặc định.
- Ghi chú đầy đủ kèm URL và trạng thái VERIFIED / PARTLY / UNVERIFIED nằm trong `scratchpad/research_pub/*.md`.

## 1. Vị thế và novelty

| Đóng góp | Kết luận | Gần nhất | Paper đó KHÔNG làm gì |
|---|---|---|---|
| C1. Bối cảnh nâng cấp theo giai đoạn: fleet học bị mất lợi ích khi đèn thành đèn học | PARTIAL | Stevanovic TRR 2013; NYSERDA 19-08 (2019); Jiang–Zhang–Wang 2022; Paine (Southampton, 06/2025) | Không đóng băng hai quần thể học, không đo so với σ*, không sửa mà không train lại |
| C2. Forecast tự phá vì xe glide ra khỏi bộ đếm halting | PARTIAL (ý chung: Bottom, Perdomo); NOT FOUND (cơ chế cụ thể) | Maadi et al., Sensors 2022; Malena et al., ITSC 2025; Paine 2025 | Đèn được train lại; không publish forecast; không đo publish so với shadow |
| C3. Provider phía fleet: exact-in-yellow + quantile theo trạng thái | **COLLIDED ở cấp thành phần** | **EP3985636 (2020): QRNN điền minEnd/likely/maxEnd bằng quantile 5/50/95**; Genser, Eteifa, Bodenheimer, Malena | Không nhắm đèn RL, không train hay đánh giá vòng kín, không trọng số theo truy vấn, không ghép với adapter |
| C4. Adapter đầu vào trước controller đã đóng băng | **COLLIDED ở cấp họ phương pháp** | DC-Ada 2026; **MATES (arXiv 2609.26010, 09/2026)**; Huang ICAPS 2026; ReasonLight 2026 | Không có đối tác bị đóng băng; adapter học bằng gradient/RL; không phải phép đếm vật lý 2 tham số |
| C5. Sửa cả hai interface, cả hai policy đều đóng băng | **NOT FOUND** | CoTV, HONEST-CAV, Busch 2023, Han TRC 2026, DHCP, FoRL | Đều train chung hoặc train lại ít nhất một phía |

**Claim novelty an toàn:** "Theo các tìm kiếm đến 06/10/2026, chưa có công trình nào giữ đóng băng cả đèn học (được nâng cấp độc lập) lẫn fleet eco-driving học, rồi khôi phục lợi ích chỉ bằng việc hiệu chỉnh hai interface, với forecast tự phá được đo bằng so sánh publish và shadow. Từng thành phần riêng lẻ đều đã có tiền lệ gần." Không dùng "first".

**Phải trích thêm:**
- MATES;
- EP3985636;
- Paine 2025;
- Maadi 2022;
- Malena ITSC 2025;
- Stevanovic 2013;
- NYSERDA 19-08;
- Jiang 2022;
- Busch ICMLA 2023;
- tùy chọn: UGAT, Kwesiga 2603.15283, Linker 2017, Loos 2011.

## 2. Tính thực dụng

**Tiền đề có thật nhưng yếu hơn cách intro đang viết.**
- Chủ sở hữu tách biệt là có thật: Audi TLI và TTS ở Düsseldorf và Mỹ; Ottawa EcoDrive; Talking Traffic ở Hà Lan. Thực tế có **ba bên**: thành phố, bên trung gian làm forecast (TTS) và OEM.
- Đèn RL mới ở mức pilot một nút (KI4LSA Lemgo). Google Green Light chỉ là tư vấn retiming offline. Surtrac không phải RL.
- → Viết "adaptive and, in pilots, learned signals".

**SPaT:**
- Thực tế các controller actuated thường điền minEnd = now và maxEnd = now + 3600 s, tức không mang thông tin.
- Quantile của TSI ánh xạ được vào minEndTime / likelyTime, đây là một lập luận về khả năng triển khai.

**Trễ:**
- Kênh thương mại chủ đạo (cloud/cellular) có lẽ trễ khoảng 1 s hoặc hơn (UNVERIFIED về con số end-to-end).
- Ở 1 s, TSI chỉ giữ khoảng 1/4 phần tiết kiệm → **điểm yếu thực dụng lớn**; phải nêu rõ là cần kênh roadside trễ thấp hoặc provider bù trễ.
- Mất gói 20 % là bi quan so với ITS-G5 thực tế (2–10 %).

**Cảm biến:**
- Đếm xe theo dải vận tốc khả thi bằng radar hoặc video advance (Smartmicro, Wavetronix); đường đưa dữ liệu xe vào controller đã được demo (Purdue).
- Nhưng **adapter cần thành phố hoặc nhà cung cấp cài đặt**: "không train lại" ≠ "không cần hợp tác".

**Cơ chế:** chưa có bằng chứng thực địa về việc xe glide "biến mất" khỏi bộ đếm; cơ chế này riêng cho input dạng halting count.

**Phát thải:**
- COLOMBO D4.3 (2015, so với HBEFA3) đánh giá PHEMlight tốt hơn cho coasting, mà PHEMlight5 lại đảo kết quả của TSI.
- → Không được claim tiết kiệm nhiên liệu thực tế. Phần còn đứng được là lợi ích riêng của fleet dưới đèn fixed-time (−5.4 % / −4.4 %), cỡ GLOSA thực địa (Ottawa trung bình 5 %).
- Mặc định của SUMO 1.27.1 là HBEFA4/PC_petrol_Euro-4 (runtime check, ledger), trong khi tài liệu SUMO ghi HBEFA3 → paper phải trích phép kiểm runtime.

## 3. So với chuẩn reviewer (TR-C / T-ITS)

| Mặt | Chuẩn | Paper này | Khoảng cách |
|---|---|---|---|
| Mạng | ít nhất 1 mạng thực | 3 bản synthetic pass, spider một làn fail | LỚN |
| Mô hình phát thải | 1 mô hình đã kiểm định | HBEFA4; đảo dấu dưới PHEMlight5 | LỚN |
| Mô hình lái | Krauss hoặc ngẫu nhiên hóa | thiết kế fail dưới IDM | TRUNG BÌNH–LỚN |
| Họ đèn học | nhiều controller RL | một họ DQN (+ MP, FoRL port) | TRUNG BÌNH |
| Penetration | quét dải | 25/50/75 % | NHỎ–TB |
| Demand | có hiệu chỉnh hoặc biến thiên | randomTrips đều, 1 giờ | TB |
| Thống kê | mean ± sd | đăng ký trước, crossed bootstrap, NI, replication | **VƯỢT chuẩn** |
| Code | công khai | chưa công khai | NHỎ |

**Phản biện dễ gặp, xếp theo mức nghiêm trọng (chi phí sửa):**
1. Kết quả fuel là artefact của HBEFA4 (thêm mô hình thứ 3 trên cùng trajectory + phân tích; rẻ–TB).
2. Chỉ có mạng synthetic (InTAS/Ingolstadt hoặc RESCO; lớn).
3. IDM (hiệu chỉnh lại forecaster/adapter dưới IDM, policy vẫn đóng băng; TB).
4. Chỉ một họ đèn học (một đèn học dùng input pressure, dự đoán là không cần adapter; nhỏ–TB).
5. Tại sao không co-train (chỉ cần sửa chữ).
6. Port của comparator không công bằng (FoRL κ = 0 đang chạy; DCA-task).
7. Penetration (thêm 10 %, 100 %; nhỏ).
8. Kênh SPaT phi thực tế (broadcast định kỳ; TB).
9. Demand phẳng (thêm profile giờ cao điểm; nhỏ).
10. Fleet là PPO residual trên luật nền (chỉ cần sửa chữ).
11. Thống kê lạ (primer + bảng mean ± sd).
12. Lean lạc đề (dời vào phụ lục, giữ 1 đoạn).
13. Thiếu prior art (Paine, Malena, MATES, patent).
14. Không có code (Zenodo DOI).

## 4. Venue

| # | Venue | Deadline | Độ dài | Ghi chú |
|---|---|---|---|---|
| 1 | **Transportation Research Part C** | rolling | khoảng 10–12k từ + phụ lục online (UNVERIFIED) | hợp scope nhất; preprint được phép; abstract ≤ 250 từ + highlights |
| 2 | IEEE T-ITS | rolling | 10 trang, tối đa 16 (phí trang dư) | single-anonymous; được đăng arXiv kèm ghi chú |
| 3 | IEEE OJ-ITS | rolling | khuyến nghị ≤ 10 trang | open access, có APC |
| 4 | IEEE ITSC 2027 (Boston, 21–24/9) | **01/03/2027** (VERIFIED) | 6–8 trang | double-blind; **cấm "manuscripts generated by LLMs" (quy định 2026)** |
| 5 | IEEE IV 2027 | 15/11/2026 | 6–8 trang | không khuyến nghị |
| 6 | MT-ITS 2027 | 20/12/2026 | 6–8 trang | — |
| — | Đã đóng | — | — | TRB 2027, AAMAS 2027, ICLR 2027 |

**Khuyến nghị:**
- **TR-C** là chính, **T-ITS** là dự phòng.
- Đăng arXiv (eess.SY; cs.LG, cs.MA) cùng ngày nộp.
- Code, Lean, protocol và ledger đưa lên Zenodo có DOI.
- **Bắt buộc kiểm chính sách AI-use** của Elsevier/IEEE và khai báo trung thực.

## 5. Việc cần làm

**Chỉ sửa chữ (làm ngay):**
- Trích các paper ở mục 1.
- Sửa wording về đèn học, bên thứ ba, sự hợp tác của thành phố, trễ 1 s, PHEMlight.
- Gắn nhãn "HBEFA4 fuel" cho mọi claim fuel; ghi rõ phép kiểm runtime cho lớp phát thải mặc định.
- Abstract ≤ 250 từ; thêm highlights.
- Thêm bảng mean ± sd.
- Lean vào phụ lục.

**Thí nghiệm, theo tác động lên publication:**
- (a) Phân tích mô hình phát thải: mô hình thứ 3 trên cùng trajectory, giải thích idling so với glide → rẻ, chặn phản biện #1.
- (b) Một mạng thực (InTAS hoặc RESCO Ingolstadt) → đắt nhưng chặn phản biện #2.
- (c) Hiệu chỉnh lại dưới IDM.
- (d) W12: PPO-0 (đang chạy), DCA-task, S1, S2: củng cố claim về comparator và cơ chế, nhưng **không** chặn hai phản biện nặng nhất.
