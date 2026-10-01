**Review khoa học sáu paper — 19/09/2026**

Phạm vi: các bản `research/papers/_tex/{master,functional,query,structural,support,d6}.tex` hiện trên đĩa, phần Adaptive liên quan, các theorem/giả thiết Lean gánh headline và artifact thí nghiệm. Không compile lại, không thay manuscript hoặc source Lean. Results chính lấy từ JSON có sẵn. Hai diagnostic nhỏ đã thực hiện trong quá trình review được lưu riêng, không trộn vào panel gốc; sau yêu cầu không chạy lại, không mở thêm phép chạy. Đánh giá novelty là so sánh với các công trình tìm được, không phải chứng nhận rằng không tồn tại prior art.

**Quyết định đề nghị**

Ưu tiên một bài kết hợp **D6 sharp margin + Functional extrema-aware certification**: “Khi nào xếp hạng từ quan sát nhiễu thật sự chứng nhận compression tối ưu?” Đây là cùng một quyết định cuối cùng, nên hai phần bổ sung cho nhau. D6 cung cấp điều kiện hình học và tính sắc; Functional cung cấp hình học của bằng chứng thống kê cần thu. Không nên ghép sáu abstract thành một framework rồi gọi số lượng theorem là novelty.

Một hướng thứ hai có triển vọng là **Support + Query**, với MASTER làm ví dụ về kênh quan sát thiếu thông tin: đo chi phí của việc tìm một quyết định an toàn dưới các kênh đo được phép. Nhưng công thức max–min cho multiple correct answers đã có; novelty phải nằm ở luật cụ thể do support geometry và lớp query tạo ra.

Structural có hướng riêng mạnh hơn bản hiện tại: **giá của ràng buộc retention đều**. Review này tìm được cận dưới và construction đạt cận cho mọi m; xem `STRUCTURAL_UNIFORM_RETENTION_PROOF_20260919.md`. Đây là chứng minh toán mới, chưa formalize trong Lean. Không cần đợi một theorem tiệm cận mới để sửa phát biểu sai rằng marginal constraint không ảnh hưởng optimum.

Nếu nộp hôm nay: chọn scope D6–Functional hẹp, không tuyên bố adaptive Γ-optimality, không đưa bất kỳ phép ghép chưa chứng minh nào thành theorem đã có. Structural mới là ứng viên nghiên cứu tiếp, không tự động thay thế manuscript đang nộp.

**Sáu chain đang có gì đáng giữ**

| Chain | Kết quả có nội dung | Điều làm novelty hiện tại yếu | Vai trò đề nghị |
|---|---|---|---|
| Functional | Proxy extrema cố định có thể sai vô hạn theo cả hai chiều; alternative Top-k thật là hợp hữu hạn các polyhedron | “Non-mean statistic”, KKT PSD và best-group identification tự chúng không mới; chưa có thuật toán mới thắng C_lucb | Hình học của chứng nhận thống kê trong bài D6–Functional |
| D6 | Margin 2δ đủ cho Top-C tối ưu; construction thật đạt exchange bound dưới ngưỡng | Phần đầu về tổng bình phương và tối ưu affine là sơ cấp, đang lấn headline sắc hơn | Trục theorem chính của bài ưu tiên |
| Query | Cùng world, đổi phép đo có thể đổi bậc xuất hiện của tín hiệu; kiểm nghiệm H² theo h^(2r) | Transfer Hellinger → testing và singular-mixture rates đã quen thuộc; chưa tối ưu trên cả lớp query | Cơ chế tốc độ cho bài Support–Query |
| Support | Geometry của safe decisions; obstruction và query depth không quyết định lẫn nhau; decide–recover separation | “Decide without identifying” có prior art trực tiếp; minimax Lean còn là template chưa nối decoder thật | Xác định quyết định nào cần chứng nhận trong bài Support–Query |
| Structural | Exact free randomization law; prefix geometry; witness actual χ≥5 riêng | Nhầm menu chọn sau budget với randomization trước budget; nhầm tổng marginal với từng marginal | Chuyển sang constrained retention law, xem chứng minh mới |
| MASTER | Null directions của ordinary measurements; exact allocation có calibration trong họ đồng nhất | Square-root allocation là kinh điển; unknown offset không nhận dạng cũng là estimability quen thuộc | Ví dụ/phần ứng dụng về observation design, chưa nên là bài độc lập với claim hiện tại |

Adaptive: giữ như phần công cụ hoặc appendix. Layer-cake và sub-Gaussian concentration là kết quả nền; phản ví dụ cho một tracker chỉ đáng headline nếu phân tích rule và hậu quả mới được đóng đầy đủ.

**Audit Lean: compile sạch không đồng nghĩa câu chuyện đã đóng**

18 module headline mới/quan trọng được đối chiếu receipt, hash source hiện tại và log: **133 axiom prints, exit 0, hash khớp, không tiên đề ngoài propext/Classical.choice/Quot.sound**. Đây là kiểm tra bằng chứng compile đã lưu, không phải clean rebuild toàn corpus. Các bridge cũ về sharp margin, actual obstruction/query và anytime path cũng có olean mới hơn source, log sạch trong phạm vi đã kiểm.

Các lỗ khoa học vẫn còn:

- `LeanQueryAnalyticLimitV1.hellinger_ratio_tendsto` nhận pointwise limit, dominating envelope và identity của H2 làm giả thiết. File import Mathlib; chưa thấy theorem thay các giả thiết bằng mật độ Gaussian-mixture thật trong chuỗi đang trích. `H2` ở đây là một hàm nhận sẵn, không tự động là Hellinger đã chuẩn hóa. Cần một theorem đóng trên `p_A,h`, `p_B,h`, có hệ số factorial và normalization đúng.
- `LeanSupportMinimaxLowerV1.equivariant_is_minimax` nhận `hconst` và `hopt`. Rule có kiểu `Obs → Act`; decoder “uniform trên unexplored tips” là randomized kernel. Cần dựng kernel, chứng minh normalization, posterior risk, Bayes optimality và tính bất biến dưới phép hoán vị cho chính law của transcript. Bayes-optimal deterministic tie breaking không tự động minimax.
- `LeanAdaptiveOnlineQuotaFailsV1.greedy_steps` có kết luận **True**. Những phép so sánh bên trong không được xuất ra thành chứng minh rằng một recursion thật đi tới counts đã nêu. `online_quota_fails` chỉ ghép tổng weights, tổng counts và deficit. Vì vậy theorem hiện tại chưa chứng nhận reachability của tracker.
- `LeanAdaptiveExpectedStoppingV1.expected_stopping_le` nhận `tau : Ω → ℕ` và geometric tail. Dùng τ có giá trị tự nhiên đã loại giá trị vô hạn khỏi kiểu; đây không phải proof termination của hitting time có thể vô hạn. Cần định nghĩa hitting time trong ℕ∞, chứng minh hữu hạn a.s., rồi chuyển kiểu và ghép tail từ thuật toán thật. Adaptive matching regret và tốc độ kỳ vọng Γ đầy đủ vẫn chưa đóng bởi module này.
- `LeanFunctionalScalarProxyFailsV1` chứng nhận nhiều bất đẳng thức của hai construction, nhưng các theorem headline cuối chỉ lượng từ trên η và biểu thức số; `Jfull` ở các wrapper nhận bound làm input. Đừng viết rằng toàn bộ infimum trên mọi alternative đã được đóng trong một theorem end-to-end. Phần toán prose có thể hoàn thiện được; cần nối vào định nghĩa infimum thật nếu muốn claim fully machine-checked.
- `LeanD6GeneralFamilyV1` đóng coordinatewise magnitude-floor problem. Nó không tự đóng WLOG cho toàn bộ D6 query game hoặc adaptive unknown-A problem. `LeanD6DesignDerivationV1` affine cho một alternative cố định; min trên nhiều alternative có thể có nghiệm ở giữa đoạn.

**Các lỗi ảnh hưởng trực tiếp đến submission**

1. **Structural: hai protocol khác nhau.** `structural.tex:134–137` liên hệ K-adaptability rồi nói m−1 schedules cần thiết. Nhưng construction một defect ở mỗi budget cho phép chỉ hai schedules π_j, π_l, j≠l, phủ mọi budget với regret 0 khi được chọn schedule sau khi thấy budget. Cả hai không xấu tại cùng budget. Do đó minimum adaptive menu ở family này là 2, còn m−1 là giá trị/size liên quan randomization với thứ tự lượng từ khác. Các công thức V_avg và V_path vẫn giữ được. Không dùng tỷ số của chúng để suy ra K-adaptability menu size.

2. **Structural: uniform marginal không phải column sum.** `structural.tex:222–223,1259–1260` suy rằng uniform target không loại menu nào từ identity tổng x_{i,k}=k. Sai. Ngay budget 1, một ranking tất định thỏa tổng nhưng không thỏa x_{i,1}=1/m. Quan trọng hơn, review này chứng minh giá trị constrained tăng theo luật chẵn/lẻ; có certificate hữu tỉ cho m=5..10.

3. **Functional: inner QP thiếu g≥0.** `functional.tex:485` cho g∈ℝ nhưng kết luận min=g²/(2Σ1/w). Với g=−1, x=0 khả thi và min=0. Sửa g≥0 hoặc thay g² bằng [g]_+². Lean `inner_qp_lower` đã có hg:0≤g; lỗi ở prose. Proof family 2 cũng phải chọn z giữa hai capacity theo nghĩa không nghiêm ngặt khi alternative cho phép tie.

4. **Functional: Algorithm và implementation khác nhau.** `functional.tex:994–1028` gọi exact và ghi refine mọi ordered pair. `scripts/EXP_functional_proxy.py:j_full` chọn một pair thắng trên grid 512 điểm rồi chỉ refine pair đó. Convexity của mỗi branch không chứng minh chọn branch bằng grid là exact. 6.000-cell sweep là numerical evidence; chưa có certified global error bound. SLSQP kiểm một chiều không thay thế dual certificate. Một diagnostic độc lập đã hoàn tất trên 60 worlds từ cùng panel, refine mọi branch, không tìm thấy sai khác đáng kể: độ overestimate tương đối lớn nhất 7,43×10^-13, 0/60 vượt 10^-6. Vì vậy đây là thiếu bảo đảm và không khớp mô tả thuật toán; **chưa phát hiện số sai trong panel**. Diagnostic này cũng không phải certified solver.

5. **MASTER: experiment khác task.** `EXP_master_finite.py` dùng một binary world chung cho mọi group và prior b_g~N(0,1); headline theorem là threshold set trên Km items với nuisance không biết. Script cộng information các group, trong khi threshold task dùng bottleneck. `gamma_star` trong JSON là Δ²/(4s²), còn headline là Δ²/(2Ks²). Ví dụ đầu K=5: 0.00909909725 so với 0.00363963890, khác 2,5 lần. Body đã thêm λ=(K/2)Γ*B; abstract vẫn ghi Φ(−√(Γ*B)). RMS 0.006295 là so với finite-count predictor, còn RMS của price-law predictor là 0.009774. Không xóa simulation; đổi tên task và giới hạn điều nó kiểm.

6. **Novelty qua KKT PSD là overclaim.** `functional.tex:122–126,150–153` nói textbook certificate cần invertibility. KKT sufficiency cho convex differentiable objectives không cần M khả nghịch. Chứng minh Lean có giá trị tái lập, không tạo một định lý tối ưu lồi mới.

7. **Query: không được đồng thời nói density thật và bỏ normalization.** Introduction hiện nói các biểu thức không là densities vì bỏ normalization, trong khi abstract dùng Hellinger thật và hằng số chính xác. Tách unnormalized kernel dùng cho non-vanishing khỏi normalized p dùng cho divergence; thực hiện join, hoặc hạ claim machine-checked xuống đúng component.

8. **Citation quan trọng sai tác giả.** MASTER gán bài Bennouna cho Bennouna–Chen–Van Parys. Bài arXiv:2505.21692 và 2602.15365 là Omar Bennouna, Amine Bennouna, Saurabh Amin, Asuman Ozdaglar. Đây không phải cơ sở để đổi theorem, nhưng phải sửa trước submission vì reference đang gánh claim novelty.

9. **Structural: signed coefficients không tự loại bài khỏi nonnegative set objectives.** Với M=∑|g_i|, hàm f(S)=M−|∑_{i∈S}g_i| là không âm trên mọi subset và có đúng cùng nghiệm tối ưu theo cardinality. Vì vậy câu “incremental maximisation excludes our family because weights are signed” chưa đủ lập luận. Phải đối chiếu các giả thiết thật như monotonicity, submodularity, mục tiêu ratio và protocol; phép đổi objective này không tự chứng minh các kết quả incremental hiện có áp dụng, nhưng bác lý do loại chúng chỉ dựa vào dấu coefficients.

Các số phụ đã tính lại: Support có 10/200 simulation cells ngoài 2 standard errors, max 2.976, không phải “mọi cell trong 2”. Điều này không bác law; sửa mô tả coverage. Không cần chạy thêm seeds để sửa một câu mô tả sai.

**Bằng chứng hiện tại dùng được cho Results**

- Functional G3: 10.000 paired instances, restricted mean queries C_lucb 49.338,4892; uniform 77.940,4052; chênh −28.601,916; percentile bootstrap CI [−29.216,33604; −28.002,97964]. Certify 77,97% vs 58,15%; false-safe quan sát 0. Đây là evidence cho LUCB adaptation trên panel, không phải chiến thắng của phương pháp C_anytime hay của full oracle chưa chạy.
- Panel 1.000 trước đó: C_lucb 797 certificates/median 20.996; C_anytime 749/29.884; uniform 605/74.252. Không tiếp tục bán C_anytime là allocator mới vượt comparator mạnh nhất.
- Functional proxy: với ratio=J_full/J_scalar, 542/6000 ratio dưới 1/2, 198/6000 trên 2; tổng 12,333%; min 0,01804, max 41,7084. 1.597 cases có `extremum_moves=true`. Giữ là numerical sau khi sửa mô tả solver; hai family toán mới là chứng cứ không thể sửa proxy bằng một hằng số.
- D6 reference: exact-rational evaluations ở nhiều reference hữu ích để chỉ domain của sharpness. Khi `topC_is_A=false`, `doubled_regret` đang đo loss(A)−loss(Ac), không phải regret của tập Top-C thực tế. Không dùng các hàng đó để kết luận Top-C còn thất bại.
- Query: 600 cells / 200 instances, orders 1–3, tail slope lệch 2r tối đa 0,0336. Đây là kiểm local law. So sánh 8,8× ở h=0,6 chịu cả hệ số và crossover; không phải một phép đo riêng của lợi thế exponent.
- Structural: DP kiểm law tự do tới m=120 là tốt. Thêm certificate uniform-retention của review này để thay một statement sai bằng câu hỏi khoa học có answer cụ thể; không thay proof mọi m bằng census.

**Cách ghép D6–Functional thành một chain có ý nghĩa**

Ký hiệu δ_I là bound mixedDifference đúng định nghĩa D6; dùng α cho xác suất lỗi, tránh nhầm hai δ. Với |T|=k và margin ρ=min_{i∈T,j∉T}(C_i−C_j), theorem hiện tại cho

    2[L_F(T)−L_F(S)] ≤ |T\S|(2δ_I−ρ),  |S|=k,

khi T là Top-C và có các giả thiết product reference trong Lean. Vì vậy

    regret_F(T) ≤ (min(k,m−k)/2) [2δ_I−ρ]_+.

Construction steered cân bằng đạt exchange equality tại corner, với δ_I=1 và 1≤ρ<2. Đây là sharpness của hằng số phổ quát, không phải mọi instance dưới ngưỡng đều thất bại.

Nếu simultaneous confidence intervals cho capacity là [L_i(t),U_i(t)], đặt

    ρ_lower(t)=min_{i∈T} L_i(t)−max_{j∉T} U_j(t).

Nếu có δ_upper≥δ_I và dừng khi ρ_lower≥2δ_upper thì trên confidence event, T là Top-C và compression-optimal. Do đó P(đã cấp certificate nhưng sai)≤α. Cận ε-regret dùng thêm điều kiện ρ_lower≥0 để bảo đảm đúng premise Top-C, rồi thay ρ bằng ρ_lower và δ_I bằng δ_upper ở cận trên.

Bridge này là suy luận toán ngắn từ theorem đã có; chưa có một artifact chạy full experiment “noise → certificate → true compression loss” trong các panel mình kiểm. Không cần tuyên bố expected Γ rate để có theorem an toàn này.

Full-extrema oracle cho việc vượt margin threshold τ=2δ_upper phải dùng **certificate boundary**, không dùng rank tie boundary cũ:

    Alt_τ(T)={λ: ∃i∈T,j∉T, C_i(λ)−C_j(λ)≤τ}.
    J_τ(w,θ)=min_{i∈T,j∉T} inf_{z≥0} [S_i(z+τ)+E_j(z)].

Lý do: C_i≤C_j+τ tương đương tồn tại z≥0 sao cho C_i≤z+τ và C_j≥z. Với diagonal Gaussian energy, các row tách được. S_i là chi phí thu range vào interval; E_j là min trên mọi ordered pair mở rộng range. Phải formalize equality tổng quát này trước khi gọi là oracle đã chứng nhận.

Hai giới hạn cần giữ:

- Alt_τ là boundary của một sufficient certificate, không nhất thiết trùng boundary “compression decision thật bị sai”. Γ_τ không tự động là complexity tối ưu cho compression.
- Bảng response tự do của Functional là lớp rộng hơn response do một F thật sinh ra. Product responses thỏa mean-consistency giữa các row. Cần giao các pair regions với realizability constraints, hoặc dùng free oracle như relaxation/conservative certificate và nói rõ. Không chuyển lower bound của lớp tự do thành lower bound của lớp F bằng lời.

Khi δ_I chưa biết, phải có evidence riêng cho nó hoặc một bound từ cấu trúc F. More scalar capacity samples không tự chứng minh được interaction bound; các same-Q constructions của repo giải thích vì sao.

Figures tối thiểu: (i) sharp margin vs true compression loss; (ii) hai family proxy hỏng hai chiều; (iii) certificate cost/rate với cùng target compression; (iv) feasible reference region. Hiện (i),(ii),(iv) có nguyên liệu, (iii) mới có range-identification panel chứ chưa có full chain.

**Support–Query–MASTER: hướng dài hơi, không gán novelty cho framework đã có**

Đặt A_ε(F) là tập decisions an toàn và P_F^q là law của query q. Mục tiêu là gom uncertainty vào một tập có giao A_ε khác rỗng, không phải identify F. Candidate information value:

    Γ_dec(F)=max_{a∈A_ε(F)} sup_w inf_{G:a∉A_ε(G)} Σ_q w_q KL(P_F^q||P_G^q).

Đây là dạng multiple-correct-answers đã được Degenne–Koolen nghiên cứu, không phải phát minh của repo. Phần đáng thử là tính nó hoặc tìm exponent của nó cho support geometry và query class thật.

Với hữu hạn worlds/queries, fixed costs và coefficient không suy biến, xét order r_q(F,G) của KL~h^(2r). Candidate exponent:

    r_dec(F)=min_{a∈A_ε(F)} max_{G:a∉A_ε(G)} min_q r_q(F,G).

Đây là mục tiêu cần prove cả upper/lower, không phải theorem hiện có. Nếu muốn uniformity theo h, phải kiểm hệ số và các giới hạn; không đơn giản thay một asymptotic theo α bằng h→0. So sánh với exponent identify-all có thể cho một separation mạnh hơn coupon-collector example.

Ba việc cụ thể: tạo 3-world safe-set geometry thật; gắn normalized query laws có order 1/2/∞ lên cùng worlds; thiết kế rule dừng khi còn một common safe action. Giữ cùng noise, query cost, amplitude bound và world pair. Nếu không ràng buộc magnitude/query cost, “query tốt hơn” có thể chỉ là khuếch đại tín hiệu.

MASTER cần đổi câu hỏi thành calibration phụ thuộc task. Với observations θ_ra+b_r, range invariant: range(θ_r+b_r 1)=range(θ_r). Không thể nói anchor bắt buộc cho range. Với threshold tuyệt đối thì không invariant. Sự khác biệt task này là một ví dụ tốt, nhưng theorem estimability chung vốn đã có trong thống kê và data sufficiency.

**Prior art cần phản hồi thẳng**

- Huang, Ajallooeian, Szepesvári, Müller (2017), Structured Best Arm Identification with Fixed Confidence: noisy micro-observables, LUCB-micro. https://proceedings.mlr.press/v76/huang17a.html
- Shahverdikondori, Badri, Kiyavash (2025), Best Group Identification in Multi-Objective Bandits. https://arxiv.org/html/2505.17869v1 . Với θ∈[0,1], phép đo vector (X,1−X) không thêm information và score max θ+max(1−θ)=1+range. Do đó Top-1 range có embedding vào objective của họ. Đây là suy luận từ model; sharp structured oracle và Top-k không tự động được giải bởi việc nhắc tới embedding.
- Jourdan, Degenne, Kaufmann (ALT 2023), Dealing with Unknown Variances in Best-Arm Identification. https://proceedings.mlr.press/v201/jourdan23a.html . Không chuyển known-variance quadratic energy thành unknown-variance optimal rate.
- Degenne–Koolen (NeurIPS 2019), Pure Exploration with Multiple Correct Answers. https://arxiv.org/abs/1902.03475 . Đã có max qua correct answers, optimal sample complexity và sticky tracking.
- Javdani et al. (AISTATS 2014), Near Optimal Bayesian Active Learning for Decision Making. https://proceedings.mlr.press/v33/javdani14.pdf . Overlapping decision regions và hyperedge cutting đã có.
- Bennouna, Bennouna, Amin, Ozdaglar (2025; related 2026 manuscript), https://arxiv.org/abs/2505.21692 và https://arxiv.org/abs/2602.15365 . Data sufficiency cho LP và least-cost sufficient data; không gán noise/combinatorial extensions nếu chưa kiểm.
- Boyd–Vandenberghe, Convex Optimization, duality lecture §KKT for convex problems. https://web.stanford.edu/class/ee364a/lectures/duality.pdf . PSD KKT sufficiency là chuẩn.
- Bate–Karp (2014), A Common Control Group — Optimising the Experiment Design to Maximise Sensitivity. https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0114872 . Shared-control square-root allocation là comparator trực tiếp hơn một tuyên bố “price of calibration chưa được nghiên cứu”.
- Ho–Nguyen, Singularity structures and impacts on parameter estimation in finite mixtures. https://arxiv.org/abs/1609.02655 . Order of vanishing và rates trong mixtures có lịch sử lâu; điểm mới phải ở admissible measurement constraints cụ thể.
- Kurtz (2026), Bounding the optimal number of policies for robust K-Adaptability. https://link.springer.com/article/10.1007/s10107-026-02329-1 . Protocol chọn recourse sau uncertainty khác randomization-before-budget.
- Singh–Joachims (KDD 2018), Fairness of Exposure in Rankings. https://www.cs.cornell.edu/~tj/publications/singh_joachims_18a.pdf . Marginal-constrained randomized rankings đã có; Structural mới nên claim exact signed-prefix law/price, không claim phát minh fairness constraints.

**Việc cần làm theo thứ tự, không mở thêm seeds đại trà**

1. Sửa các theorem/protocol sai trong bản sẽ nộp; bỏ “every displayed theorem machine-checked” ở nơi source chỉ có template.
2. Chốt một target quyết định và một observation model cho bài ưu tiên. Gộp sharp D6 threshold với confidence certificate; đẩy square-completion/KKT/audit listing vào supplement.
3. Nếu dùng 6000 proxy cells, đồng bộ solver và algorithm description; refine mọi branch hoặc xuất primal/dual error enclosure. Không cần tăng N để giải lỗi này.
4. Figure experiment còn thiếu phải đo đúng target cuối: các world F thật, full enumeration loss để làm ground truth, capacity certificate và compression certificate được phân biệt. Include C_lucb cùng information. Không cần quảng bá allocator mới nếu chưa có.
5. Formalize Structural uniform-retention law mới nếu chọn phát triển bài Structural. Công thức và proof route đầy đủ ở file riêng. Đây là thay đổi nội dung paper, không phải tăng audit count.
6. Support–Query: chỉ mở branch measurement-order/decision-boundary sau khi đã chọn world family và normalized laws. Không làm lại generic max–min theorem và gọi nó là novelty.

Không có cơ sở đảm bảo venue accept từ compile sạch hoặc số thí nghiệm. Nhưng hiện có đủ nguyên liệu để viết một câu chuyện hẹp, kiểm chứng được; sáu câu chuyện lớn như các abstract hiện tại vẫn phát biểu rộng hơn bằng chứng ở vài mắt nối quan trọng.

**JSON hiện có dùng để viết Results — không cần chạy lại panel**

Các đường dẫn dưới đây tính từ `/Users/phanan/cig-amf-main/`:

| Artifact | Dùng được để kết luận | Không tự chứng minh |
|---|---|---|
| `research/G3_confirmatory_20260915/G3_result.json` | C_lucb vs uniform trên 10.000 paired instances và đúng stopping endpoint đã lưu | Oracle extrema mới đạt optimal Γ; compression regret thật |
| `research/paper_exp_20260916/functional_proxy.json` | Sai lệch proxy hai chiều, incidence trên panel, hai family theo η | Certified global optimum của mọi nghiệm float |
| `research/paper_exp_20260916/d6_reference_wide.json` | Response và designated-set losses theo reference; các case exact có điều kiện Top-C đúng | Top-C regret ở các hàng mà Top-C đã đổi khỏi A |
| `research/paper_exp_20260916/query_generalize.json` | Local slopes và hệ số trong các measurement families được chạy | Tối ưu trên mọi query được phép; adaptive transcript theorem |
| `research/paper_exp_20260916/support_thresholds.json` | Kiểm law hữu hạn, threshold và empirical risk trong thiết kế đã chạy | Concrete randomized minimax theorem chưa instantiate |
| `research/paper_exp_20260916/master_finite.json` | Finite-count prediction trên common-binary-world simulation | Headline threshold-set task với nuisance tự do |

Các diagnostic của review nằm cùng thư mục với báo cáo: `cig_scientific_checks_20260919.{py,json}` và `cig_functional_allpair_check_20260919.{py,json}`. Không ghi đè artifact cũ, không tự nâng evidence class của panel cũ.
