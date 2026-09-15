# Các hướng nghiên cứu sau kiểm tra construction và thí nghiệm

Mục tiêu có triển vọng nhất là tìm một luật định lượng mà geometry, query được phép và ngân sách cùng quyết định; tên gọi mới cho một bài toán active learning có sẵn không đủ. Các kết quả dưới đây tách rõ proof Lean, kiểm tra hữu hạn exact, thí nghiệm phát triển và conjecture. Không kết quả simulation nào được dùng thay cho cận tối ưu adaptive, termination hoặc tốc độ kỳ vọng Γ.

## Kết quả thực hiện trên sáu paper

| Paper | Kết quả mới | Điều bị bác bỏ hoặc thu hẹp | Hướng có giá trị tiếp theo |
|---|---|---|---|
| MASTER | Contract cụ thể có sound suy ra từ membership support thật; probe 40 world hoàn tất | Certificate rẻ về thông tin không đồng nghĩa nhanh về runtime; transfer runner vẫn dùng Gamma_op | Tối ưu tổng chi phí acquisition + tính certificate, với sound cụ thể và chi phí đo thật |
| Functional | 12 cặp instance, cố định gap ngoài/noise, đổi gap cực trị; anytime giảm 9.167 → 5.700 mẫu | Gap Top-k không mô tả hết chi phí của runner; shrink không mặc nhiên là đóng góp | Luật hai thang: xác định các cực trị liên quan và chứng nhận lựa chọn; đối chiếu LUCB-micro |
| Support | Họ obstruction bậc m trên support hai điểm, bền tới epsilon=1/2; một membership query vẫn đủ | Bậc obstruction không thể đứng một mình làm độ phức tạp acquisition | Tham số kết hợp hình học tập quyết định và khả năng phân tách của query |
| Structural | Lean: một ranking đạt 1/(2r) trên staircase chuẩn hóa; tìm witness scalar mới bằng DP exact | Exact chi=r không chứng minh robust chi lớn; witness mới tìm được chỉ cần hai ranking | Cận khớp cho số ranking ở epsilon cố định trên họ chuẩn hóa, hoặc một universal upper bound |
| D6 | Lean: thiết kế cyclic A-free, law Gaussian thật, cận dưới variance cho linear statistic; tìm họ block ngắn | Ba query/hệ số 9 không phải thiết kế tốt nhất ở mọi budget; equal weights không WLOG | Luật thiết kế theo ngân sách nguyên, trọng số và q; sau đó mới ghép phase loss/adaptive regret |
| Query | 336 ô regret-evaluable trên 12 fixture giao hàng; reset/warmup vẫn 0 | Tăng horizon một mình không chữa được state/policy không có tín hiệu; chưa có natural-trajectory transfer | Điều kiện tín hiệu theo khoảng cách–horizon–policy, rồi kiểm tra trên state bank độc lập |

## D6: chuyển từ một construction sang luật theo ngân sách

Đặt n=2q+1 là số coordinate ngoài j. Với off query G hợp lệ, mean của observation là

\[
 m_G=1+|G\cap B|(1-\mu),\qquad |B|=q.
\]

Construction cyclic dùng n query, mỗi query chứa q coordinate và mỗi coordinate xuất hiện q lần. Vì thế tổng mean là n+q²(1−μ), đồng thời tổng noise có variance n. Với L block độc lập, N=Ln, estimator không biết A có

\[
\widehat\mu=\frac{Ln+Lq^2-\sum Y}{Lq^2},\qquad
\operatorname{Var}(\widehat\mu)=\frac{n^2}{q^4N}.
\]

Các mệnh đề về query hợp lệ, tổng actual mean, law trên product measure và variance đã compile. Phía dưới cũng đã nối vào actual Gaussian observations: mọi fixed linear statistic có coefficient bất biến trên tất cả q-subset thỏa

\[
\operatorname{Var}(\widehat\mu)\ge\frac{|U|^2}{q^4N}.
\]

Cận này cho phép trọng số âm. Đây là matching trong lớp statistic tuyến tính bất biến A, trên off queries với noise độc lập variance 1. Nó chưa là matching regret cho mọi adaptive policy; cũng chưa chứng minh học A, termination hoặc Γ.

Probe raw Gaussian chạy q=3,4,8,16,32,64; L=1,4,16; 20.000 trial/cell, tổng 36 cell. Tỷ số variance thực nghiệm/lý thuyết nằm trong [0,98865; 1,02200]. Hidden B được chọn ngẫu nhiên một lần cho mỗi q; tính đồng nhất trên mọi B đến từ proof và kiểm tra incidence, không từ số seed.

### Construction block ngắn và proof toán học cần formalize

Chọn 1≤d≤q và b=2d+1. Đánh số coordinate i=0,...,n−1. Cho coordinate i xuất hiện ở các hàng

\[
 id, id+1,\ldots,id+d-1\pmod b.
\]

Vì d<b, mỗi coordinate xuất hiện đúng d lần, không lặp trong một hàng. Ghép các đoạn này tạo đúng d·n token liên tiếp. Do đó kích thước mỗi hàng bằng floor(dn/b) hoặc ceil(dn/b). Bất đẳng thức dn≤bq tương đương d≤q, nên mỗi hàng có nhiều nhất q coordinate. Nếu d≥2 thì dn/b≥d≥2; nếu d=1 thì n≥7 và floor(n/3)≥2. Tất cả hàng là off query hợp lệ.

Tổng mean bằng b+dq(1−μ). Với L block, variance là b/(L d²q²), hay hệ số so với oracle 1/(q²N) là

\[
\left(2+\frac1d\right)^2.
\]

Đây là proof construction bằng số học; module Lean cho toàn bộ d chưa được viết. Kiểm tra hữu hạn đã qua 973 thiết kế tại q=3,...,32,64,128,256, gồm 2.919 phép kiểm hidden-label trực tiếp ở q≤5. Phần lớn thiết kế dùng incidence identity để kiểm mọi hidden subset đồng thời.

Có một hướng lower bound sắc hơn cho số query lẻ 3≤N≤2q+1 trong lớp tổng không trọng số. Nếu tổng mean bất biến trên mọi q-subset, degree của mọi coordinate phải bằng nhau: so hai q-subset chỉ khác một coordinate. Gọi degree nguyên là d; đếm incidence cho nd≤Nq, nên d≤floor(Nq/n)=(N−1)/2. Variance N/(q²d²) vì vậy bị chặn dưới bởi 4N/[q²(N−1)²], và construction trên đạt dấu bằng. Cần formalize phép đổi một coordinate và toàn bộ cardinal bounds; đây chưa là một theorem Lean đã audit.

**Không được mở rộng lower bound này sang trọng số tùy ý.** Một construction bốn query dùng trọng số (1/2,1/2,1/2,1). Chia q+1 coordinate đầu thành ba loại, mỗi loại thuộc một cặp trong ba query đầu; q coordinate còn lại thuộc query cuối. Phân phối ba loại cân bằng cho mọi q≥3. Mỗi coordinate có tổng trọng số 1, variance estimator bằng 7/(4q²), tức penalty 7 ở N=4. Script kiểm tính hợp lệ bằng số nguyên. Global optimality cho bốn query chưa được chứng minh.

Thiết kế linear tối ưu đã là lĩnh vực lâu đời, bắt đầu ít nhất từ Elfving. Phần có thể thành đóng góp ở đây là lời giải cụ thể có ràng buộc legality, ngân sách nguyên, nuisance A, và cách nó đi vào phase/regret của D6; riêng Cauchy–Schwarz hoặc cân bằng incidence không phải novelty mới.[^elfving] Kết quả Degenne về fixed-budget complexity cũng không tự chứng minh estimator này optimal: định nghĩa và lượng từ của bài đó khác lớp linear invariant đang xét.[^degenne]

## Support và MASTER: obstruction lớn nhưng quyết định rẻ

Với m≥2, dùng cùng các primitive là phép chiếu coordinate. World w có support {0,t_w}, trong đó coordinate w của t_w bằng 2−m, còn tất cả coordinate khác bằng 1. Tổng coordinate của tip là 1. Nếu giữ relation j thì actual selectedRadius bằng 0 khi j≠w, và bằng (m−1)/2 khi j=w.

Mọi proper subfamily có chung một quyết định zero-regret: giữ index của một world bị bỏ khỏi subfamily. Cả m world không có quyết định chung. Tổng component radius là (2m−3)/2, đã được chứng minh trong Lean từ osc của các component. Sau chuẩn hóa, quyết định sai có radius

\[
\frac{m-1}{2m-3}>\frac12.
\]

Vì vậy obstruction không biến mất ở sai số cố định 1/2 khi m tăng. Nhưng hỏi membership của t_a là đủ: nếu có thì world=a và chọn b≠a; nếu không thì chọn a. Lean đã chứng minh membership iff world=a từ support point thật, rồi chứng minh selectedRadius=0. Contract MASTER nhận tính đúng của observation làm obligation; sound được dựng từ theorem geometry này, không nhập một giả thiết regret.

Phạm vi rất quan trọng: đã biết world thuộc họ m support liệt kê và đúng một non-anchor tip hiện diện. Đây không phải thuật toán giải arbitrary unknown support. Trong mô hình flip membership độc lập xác suất eta<1/2, lặp query đó số lần lẻ ít nhất log(1/delta)/[2(1/2−eta)²] và majority vote cho cận lỗi Hoeffding, độc lập m. Probe tới m=128, eta=0,1/0,25/0,4 cho tỷ lệ false-safe lớn nhất 0,0074 với delta=0,05; mỗi cell 20.000 trial.

Bài toán decision regions chồng lấn đã được Javdani và cộng sự giải bằng HEC; equivalence fibre-safe không phải novelty.[^hec] Định lý embedding vào support-radius có giá trị làm rõ giới hạn nhưng chưa đủ kết luận standalone paper đột phá. Hướng cần kiểm là một complexity phụ thuộc cả minimal bad subfamilies và incidence của các query phân tách chúng; ví dụ này loại được mọi conjecture chỉ dùng kích thước bad subfamily.

Bennouna 2026 thực sự có Corollary 1 cho quyết định combinatorial (trang in 15) và Proposition 10 cho observation Qc+noise (trang in 52). Không thể nói họ chỉ có LP không nhiễu. Membership support chưa tự động là phép đo linear cost trong mô hình đó; cần phép giảm cụ thể trước khi kết luận trùng hoặc khác.[^bennouna]

MASTER probe 40 world cho Gamma_box/Gamma_op trung bình 0,58456; 97,5% trường hợp có tightening. Tuy nhiên active certificate trong `master_transfer` là **Gamma_op**, nên không được ghi đã hoàn tất held-out transfer của Gamma_box. Held-out coverage của score-error radius ở các cấu hình là 0,94–0,99; đây là calibration phát triển. Trong một cấu hình cascade, speedup chỉ 0,336× do certificate cost lớn hơn giải exact bài toán nhỏ. Muốn novelty thực dụng phải tối ưu tổng chi phí; cải thiện một upper bound mà runtime tăng không đủ.

## Functional: xác định thang geometry cần chứng minh

Probe mới có 3 relation, 6 action/relation, k=1, capacities (1,4;1,2;1), noise độc lập sigma=0,3. Vị trí extrema được hoán vị riêng cho mỗi relation/instance. Giữ gap ngoài 0,2, đổi gap từ cực trị tới action kế cận từ 0,01 sang 0,2; hai nhánh dùng cùng noise streams. Batch=128, max_n=16.384; đây là protocol phát triển mới, không gộp trực tiếp với runner batch=16 trước đây.

| Policy | Certify: inner gap 0,01 | Certify: inner gap 0,2 | Mean N trong trường hợp tất cả đều certify |
|---|---:|---:|---|
| uniform | 6/12 | 7/12 | Không so mean bị censor như sample complexity |
| C_anytime | 12/12 | 12/12 | 9.166,7 → 5.700 |
| C_shrink | 11/12 | 12/12 | Một nhánh còn censor |
| C_known_sigma, diagnostic | 12/12 | 12/12 | 8.953,3 → 5.508 |

C_anytime có chi phí thấp hơn ở cả 12 cặp khi inner gap lớn hơn. Không cell nào false-safe. Đây là evidence rằng runner nhạy với geometry bên trong; chưa chứng minh characteristic time tối ưu phụ thuộc tham số này theo cùng công thức. Structured BAI với micro-observables và upper/lower sample complexity đã có trong Huang et al.; phải so với LUCB-micro và các alternative set họ dùng.[^huang] Multiple-correct-answer identification cũng đã có thuật toán đạt cận tiệm cận.[^multiple]

Probe tăng max_n=65.536, 16 instance seed 8301, batch=16 đã hoàn tất riêng. Mỗi adaptive policy certify 10/16; uniform 5/16; false-safe=0. Median anytime là 38.332, uniform vẫn censor tại 65.537. Không dùng 16 instance này để khẳng định tỷ lệ tăng so với 300 instance cũ vì seed/panel khác. Pilot có median 31.335 ở panel này, thấp hơn anytime; vì vậy không có thứ hạng universal được xác nhận.

Hướng high-risk có thể kiểm tiếp: cố định gap ngoài và noise, tăng số action gần cực trị, rồi tách chi phí tìm mặt active khỏi chi phí phân biệt relation. Cần một construction mà lower bound và algorithm cùng phản ánh số mặt gần-active. Nếu chỉ là đổi tên complexity của structured BAI thì hạ claim thành specialization, không tìm một tên khác cho cùng kết quả. Wan et al. 2026 cũng đã có sequential design theo directional uncertainty và stopping-time advantage cho downstream linear optimization.[^wan]

## Structural: robust menu size còn là chỗ khó thật

Lean đã đóng cho toàn họ staircase: giữ negative relations trước, rồi positive relations, cho sai số không quá 1/2 ở mọi budget. Sau chuẩn hóa tổng component radius r, một ranking đủ tại epsilon=1/(2r). Kiểm tra exact mọi subset ở r=2,...,8 đạt đúng giá trị này cho ranking được dựng. Điều đó không chứng minh đây là minimum one-ranking error; nhưng đủ bác suy luận từ chi_exact=r sang robust hardness ở epsilon cố định.

Witness scalar cũ [-32,7,29,-7,-8,-13,18] có exact menu curve 5→3→2→1 với mốc 1/114,1/57,7/57. Lean mới chứng minh không thể dùng ≤4 ranking khi epsilon<1/114. Phần toàn bộ curve là exhaustive finite computation.

Tìm 100 vector nguyên cho mỗi m=6,8,10,12 bằng DP trên subset lattice cho hai witness có one-ranking threshold cao hơn: m=6 là 7/32; m=8 là 4/21. Nhưng exhaustive menu search sau đó cho thấy cả hai đều chỉ cần **hai** ranking tại epsilon=0. Do đó chúng không giải quyết câu hỏi robust K lớn, dù một ranking chịu sai số đáng kể. Cần giữ kết quả thất bại này trong lựa chọn hướng.

Mục tiêu có khả năng thành contribution là dichotomy: hoặc mọi objective của một lớp support geometry chuẩn hóa có cover O(1/epsilon^p) không phụ thuộc m, hoặc có construction chi_epsilon→infinity tại một epsilon cố định. Đây là conjecture cần thử, chưa phải theorem. Bằng chứng staircase mới nghiêng về việc upper bound theo tolerance có thể quan trọng hơn exact obstruction.

Đọc Kurtz phải sửa thêm một bước suy luận: n_xi là dimension uncertainty, nhưng Theorem 2 còn cần U lồi, f liên tục và lõm theo uncertainty. Budget rời rạc không thỏa U lồi; nội suy prefix có thể phá continuity/concavity. Hơn nữa, equality của worst-case robust value không tự động là optimal ở từng budget; phép giảm phải dùng excess regret và kiểm lại các giả thiết. Chưa được gọi m/2 so với 2 là một separation đã chứng minh với Kurtz.[^kurtz]

Bài incremental submodular mới tháng 6/2026 có ratio 1,373 và lower bound 1,25 cho một ordering. Đó là prior art gần với prefix quality, nhưng objective submodular/maximization và competitive ratio khác menu size của selectedRadius không monotone.[^incremental] Phải chứng minh khác biệt có nội dung toán học, không chỉ khác notation.

## Query: có tín hiệu kiểm soát, chưa có transfer trên quỹ đạo tự nhiên

Ở 12 fixture RWARE có hai carrier cách goal một bước, 48/72 state-query target không hằng; từ đó 336/504 raw method-query cell có thể đánh giá regret. Trên reset/random-warmup, con số là 0. Cả hai mẫu giữ toàn bộ state được định trước; không lọc theo query outcome.

Có khác biệt đúng theo loại query: C_response_span đạt regret 0 ở response-sensitivity nhưng 0,4 ở signed-policy-effect; D_signed_policy_projection có chiều ngược lại, regret 0 ở signed-policy-effect và 2 ở response-sensitivity. Đó là evidence về giới hạn dùng một summary cho query khác trong fixture này. Coalition/noop targets còn hằng và vẫn nằm trong denominator; không được che chúng bằng cách chỉ báo các ô có tín hiệu.

Probe khoảng cách 1/2/4, horizon 1/d/d+1, policy noop/forward trên sáu seed cố định đã hoàn tất 16 cấu hình khác nhau. Tại distance=2 hoặc 4: horizon=1 cho 0 regret cell; noop vẫn cho 0 ngay khi horizon bằng distance hoặc distance+1; forward với horizon bằng distance hoặc distance+1 cho 168 regret cell mỗi cấu hình, toàn bộ 6 state đều executable. Forward là policy cố định chọn action non-idle đầu tiên, không phải learned competent policy. Kết quả này dùng xác định khi nào target xuất hiện, rồi mới thiết kế state bank natural có policy frozen đủ năng lực.

Le Cam deficiency là một tối ưu trên simulation kernels và lớp loss, không phải regret của một chosen decoder. Ngay cả hướng gọi transfer bằng deficiency cũng đã có preprint gần đây; chỉ ghi nhận cạnh tranh khái niệm, không tiếp nhận claim “first” của tác giả.[^lecamtransfer] Hướng còn đáng làm là bridge có lượng từ rõ từ query semantics/observation budget tới worst-case target regret và một dataset có target không hằng.

## Thứ tự proof tiếp theo và tiêu chí dừng nhánh

1. **D6:** formalize short balanced incidence cho mọi d≤q; đóng lower bound ngân sách lẻ trong lớp equal weights; xét trọng số khác bằng witness bốn query trước khi tuyên bố WLOG. Sau đó ghép phase test loss vào allocation regret. Không dùng variance matching thay cho adaptive regret matching.
2. **Support/MASTER:** dùng concrete contract đã compile làm base case; mở finite-world promise sang unknown support có nhiều tip. Thử xem một query còn đủ không. Nếu không, tìm complexity phụ thuộc query partition và geometry, cùng lower bound.
3. **Structural:** tìm witness chi_epsilon≥3 ở epsilon cố định sau chuẩn hóa, đồng thời thử chứng minh universal cover upper bound. Mở rộng random search một ranking đơn thuần không đánh đúng câu hỏi này.
4. **Functional:** thêm structured-BAI baseline và đo số extremal competitors với outer gap cố định. Chỉ tăng seeds sau khi endpoint và contrast này cố định.
5. **Query:** đọc distance/horizon controls và tạo natural state panel riêng; không trộn fixture positive control với generalization evidence.
6. **MASTER:** đưa Gamma_box vào chính transfer endpoint và đo tổng chi phí trên bài toán mà exact optimization đủ đắt; tránh chỉ tăng kích thước để che một certificate không hiệu quả.

## Sources

[^elfving]: G. Elfving. “Optimum Allocation in Linear Regression Theory.” Annals of Mathematical Statistics 23(2), 255–262, 1952. [Nguồn gốc](https://doi.org/10.1214/aoms/1177729442)
[^degenne]: Rémy Degenne. “On the Existence of a Complexity in Fixed Budget Bandit Identification.” COLT 2023. [Nguồn gốc](https://proceedings.mlr.press/v195/degenne23a.html)
[^hec]: Shervin Javdani et al. “Near Optimal Bayesian Active Learning for Decision Making.” AISTATS 2014, extended version. [Nguồn gốc](https://arxiv.org/abs/1402.5886)
[^bennouna]: Omar Bennouna, Amine Bennouna, Saurabh Amin, Asuman Ozdaglar. “Data Informativeness in Linear Optimization under Uncertainty.” 17 February 2026; Corollary 1 and Proposition 10. [Nguồn gốc](https://arxiv.org/pdf/2602.15365) . Distinct from the shorter 2025 paper, [Nguồn gốc](https://arxiv.org/abs/2505.21692) .
[^huang]: Ruitong Huang, Mohammad M. Ajallooeian, Csaba Szepesvári, Martin Müller. “Structured Best Arm Identification with Fixed Confidence.” ALT 2017. [Nguồn gốc](https://proceedings.mlr.press/v76/huang17a/huang17a.pdf)
[^multiple]: Rémy Degenne, Wouter M. Koolen. “Pure Exploration with Multiple Correct Answers.” NeurIPS 2019. [Nguồn gốc](https://proceedings.neurips.cc/paper/2019/file/60cb558c40e4f18479664069d9642d5a-Paper.pdf)
[^wan]: Beichen Wan, Mo Liu, Paul Grigas, Zuo-Jun Max Shen. “Decision-Focused Sequential Experimental Design: A Directional Uncertainty-Guided Approach.” 5 February 2026; Sections 2–3. [Nguồn gốc](https://arxiv.org/html/2602.05340v1)
[^kurtz]: Jannis Kurtz. “Bounding the Optimal Number of Policies for Robust K-Adaptability.” Accessible manuscript, Theorem 2 and Sections 2–3. [Nguồn gốc](https://optimization-online.org/wp-content/uploads/2024/09/main-3.pdf)
[^incremental]: Marcin Bienkowski, Joakim Blikstad, Jarosław Byrka, Martín Costa, Yann Disser, Annette Lutz. “Incremental Submodular Maximization: Better Than Greedy.” 26 June 2026; Theorems 1–2. [Nguồn gốc](https://arxiv.org/html/2606.28558v1)
[^lecamtransfer]: Deniz Akdemir. “Le Cam Distortion: A Decision-Theoretic Framework for Robust Transfer Learning.” Preprint, 29 December 2025. [Nguồn gốc](https://arxiv.org/abs/2512.23617) . Conceptual overlap only; empirical and priority claims are not independently validated here.

Local evidence: JSON artifacts and compile logs listed in `evidence_manifest.json`, in this directory. Lean sources are in `/Users/phanan/cig-amf-main/work/p13_conjectures/`. The latest source addenda read for MASTER, Functional, Support and Query were the respective 20260908E/C/B/C files under `/Users/phanan/Downloads/CIG_AMF_EVOLUTION_REPORTS_APPEND_ONLY_20260905_DELIVERY/source_addenda/`; newer on-disk proof and experiment evidence takes precedence over those historical status statements.

## Reproduction

Mọi lệnh chạy từ `/Users/phanan/cig-amf-main`. Các JSON của đợt này đều đã được ghi; không còn job của đợt thử nghiệm chờ kết quả. Không ghi đè kết quả phát triển đã có khi chạy lại: đổi tên `--out`.

```bash
.venv/bin/python scripts/run_high_risk_geometry_probes.py d6 --out research/high_risk_20260910/d6_cyclic_raw_repeat.json
.venv/bin/python scripts/run_high_risk_geometry_probes.py support --out research/high_risk_20260910/support_repeat.json
.venv/bin/python scripts/run_high_risk_geometry_probes.py structural --searches 100 --out research/high_risk_20260910/structural_repeat.json
.venv/bin/python scripts/run_functional_extremal_geometry_probe.py --out research/high_risk_20260910/functional_geometry_repeat.json
```

`verify_d6_short_balanced_blocks.py` và `run_query_distance_horizon_probe.py` hiện dùng tên output cố định trong source; sao lưu hoặc đổi tên output trước khi chạy lại nếu cần giữ cả hai lần. Lệnh compile một module cụ thể:

```bash
cd /Users/phanan/cig-amf-main/work/p13_conjectures
LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}" lake env lean -o LeanD6BlindLinearOptimalityV1.olean LeanD6BlindLinearOptimalityV1.lean
```
