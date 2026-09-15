# Audit worker và batch tiếp theo khác bản giao việc trước

**Trạng thái đã kiểm.** Gói adaptive hiện nằm trong cig-amf-main, gồm 12 module/53 audit và 58 dependency/245 audit. Đã tính lại hash của source, binary và log; đối chiếu cả installation, report, manifest. Không phát hiện mismatch. Đây là kiểm evidence build có sẵn, không phải clean build mới. [Audit có thể đối chiếu](/Users/phanan/cig-amf-main/research/WORKER_AUDIT_AND_NEXT_BATCH_20260913.json).

Đã đọc nội dung decoder, expectation, measurability, tracker và discovery stopping. Các theorem không nhập optimizer quality làm giả thiết trong instantiation; expectation chứng minh integrability; nhãn sai vẫn bị tính loss; discovery stopping là first acceptance trên filtration quan sát được. Chưa thấy lỗi toán trong các phần này. Source và REPORT cũng giữ đúng giới hạn: chưa có scheduler toàn bộ, likelihood termination và expected Gamma. Không được nâng 53 audit thành “adaptive optimal algorithm đã đóng”.

**Lỗi đã tự sửa:** `scripts/SUPPORT_law_probe.py` vẫn thử parity union law dưới điều kiện chỉ s−1 interval có private point. Đổi bản kiểm chính sang EVERY interval, giữ legacy mode làm negative control. Phản ví dụ m=13,L=3,s=3 vẫn cho legacy H=5<7; bản sửa cho H=7. Đã chạy AST parse, toàn bộ part_F nhỏ (10/10 pass), ba invalid-domain cases bị từ chối. Hai case L=5,s=3/4 được in rõ là skipped. Phép kiểm mới fail bằng AssertionError nếu có mismatch, không chỉ in rồi exit 0. Không sửa các theorem Lean đã sạch. Union enumeration không thay thế chứng minh adversarial query depth.

**Cập nhật bản giao việc cũ:** câu decoder còn thiếu compile evidence đã lỗi thời sau acceptance mới; nó nay có 6 audit sạch và binary/source được cài về repo. Chưa thấy implementation mới cho tám mục tiêu nghiên cứu của bản blueprint dưới những nội dung đã tìm; phần mới rõ ràng trong đĩa là acceptance decoder. Không kết luận về công việc ở máy/thư mục khác chưa xem.

Sáu gói sau KHÁC tám gói trước: không làm lại full-extrema oracle, approximate-anchor menu, all-private union, boundary layer, scheduler, Gamma stopping, exact-fiber repair hay fixed-known-calibration acquisition. Các công thức mới là đề xuất có derivation; chưa được Lean kiểm. Các tên lemma mới bên dưới chỉ là tên dự kiến.

**N1. Functional — luật theo số action phải đo, không chỉ witness đổi extrema**

**Câu hỏi:** extrema chưa biết buộc allocator dành mẫu cho bao nhiêu cell, kể cả các cell có mean bằng nhau và đang không nằm ở extrema được tie-break chọn?

Cho Top-k thật T, C*=min_{i∈T} C_i. Với mỗi j ngoài T và action a, đặt
\[
 d_{ja}=\min\{C_*+\min_{b\ne a}\theta_{jb}-\theta_{ja},\quad
                  C_*+\theta_{ja}-\max_{b\ne a}\theta_{jb}\}>0.
\]

Giả thiết strict capacity gap và mỗi relation có ≥2 action. Chỉ nâng hoặc hạ cell (j,a) một đoạn d_ja sẽ làm j chạm capacity C*. Vì vậy với Gaussian known variance:
\[
 J(w)\le\frac{w_{ja}d_{ja}^2}{2\sigma_{ja}^2}.
\]
Nếu J(w)>0 thì MỌI cell của mọi outsider phải có w_ja>0. Cộng các lower bound w_ja≥2σ²_ja J(w)/d²_ja:
\[
 J(w)\le\left(\sum_{j\notin T,a}\frac{2\sigma_{ja}^2}{d_{ja}^2}\right)^{-1}.
\]

Đây không dựa vào oracle tổng quát: dựng alternative chỉ đổi một cell; evaluate energy; dùng định nghĩa infimum. Zero weight được xử lý trực tiếp bằng energy=0, không viết 1/w.

**Họ exact để thử chứng minh:** hai relation, i có hai action (0,1); j có K≥2 action đều bằng 0; unit variance. T={i} duy nhất dù extrema j bị tie. Đề xuất:
\[
 \Gamma_K=\frac1{2(2+\sqrt{2K})^2}=\Theta(K^{-1}).
\]

Proof cụ thể:

1. J concave theo weights vì inf của linear functions. Average theo permutations các K cell của j; symmetrize hai endpoints của i bằng phép λ_i↦1−λ_i với đảo indices. Mean thật và energy được bảo toàn, capacity không đổi. Suy ra WLOG mỗi endpoint i có mass a/2, mỗi cell j có mass (1−a)/K.
2. Co i xuống range z∈[0,1] tốn a(1−z)²/8. Mở j lên z tốn (1−a)z²/(4K). Các z ngoài [0,1] không cải thiện min; prove bằng clipping z.
3. Hoàn bình phương cho min_z bằng 1/[2(4/a+2K/(1−a))], với a∈(0,1). Hai endpoints a=0,1 cho J=0.
4. Cauchy hoặc square completion: 4/a+2K/(1−a)≥(2+sqrt(2K))². Equality tại a*=2/(2+sqrt(2K)).

Nếu code yêu cầu cùng số action mỗi relation, pad i bằng K−2 cell mean 1/2. Phải chứng minh sampling các cell đó không tăng optimum bằng symmetry/witness, không mặc nhiên bỏ chúng.

**Lean:** `one_cell_flip_feasible` → `one_cell_information_upper` → `outsider_all_cells_positive` → `outsider_mass_lower` → `flat_outsider_symmetrization` → `flat_outsider_exact_rate`. Dùng `pair_flip_lower`/`energy_decomposition` cho bước co/mở; phần symmetry cần equality của transformed objectives và finite Jensen, không dùng “WLOG” bằng văn xuôi.

**Evidence sau proof sketch:** K=2,4,8,16,32; so dual upper với explicit weights a*; so full oracle trên cùng instance. Plot KΓ_K và mass i, dự đoán KΓ_K→1/4, mass i≈sqrt(2/K). Không cần thêm seed để kiểm identity. Nhánh risky: phá tie bằng perturbation nhỏ rồi tìm bound uniform; nếu tỷ lệ biến mất ngay khi perturb thì claim chỉ là singular instance.

**Collision:** mọi-arm-phải-đo có cơ chế gần best-arm identification; oracle symmetry cũng là kỹ thuật chuẩn. [Huang et al., Structured Best Arm Identification](https://proceedings.mlr.press/v76/huang17a.html) là prior bắt buộc. Novelty candidate là exact law cho range-of-micro-observations và quantitative cost của unresolved extrema; riêng Ω(K) không đủ đột phá.

**N2. Structural — randomization có thật sự giảm menu size không?**

Khác gói anchor gần tối ưu: thay đổi guarantee, giữ đúng staircase đã formalize. Cho r>0 và 0≤ε<1/(2r), menu M được random trước khi budget k được chọn độc lập. Yêu cầu
\[
 \forall k\le2r:\quad\Pr\{\exists\pi\in M:\pi_{\le k}\text{ là ε-optimal}\}\ge1-\delta,
 \quad |M|\le K\text{ ở mọi outcome},\quad0\le\delta<1.
\]

**Đích đề xuất:**
\[
 K_{\rm randomized}(r,\varepsilon,\delta)=\lceil(1-\delta)r\rceil.
\]

Proof lower: staircase có r critical budgets với unique optima đôi một incomparable. Mỗi ranking hit tối đa một critical budget, nên menu size K hit tối đa K. Gọi X_t indicator hit critical budget t, có Σ_t X_t≤K pointwise. Lấy kỳ vọng: r(1−δ)≤K. API đã đọc: `normalized_epsilon_exact` trong `LeanStructuralStaircaseToleranceLowerV1`; `staircaseSelected_unique_optimal` và proof incomparability trong `LeanStructuralUnboundedPrefixCoverFamilyV1`.

Proof upper: dùng canonical menu r ranking đã có, chọn uniform K-subset của indices. Mỗi budget có ít nhất một canonical ranking cover nó; xác suất ranking đó được chọn K/r. Trước khi tính membership probability, prove r rankings distinct qua unique critical optima. Dùng finite sums trên powersetCard, chưa cần xây probability process.

**Phải kèm theorem phản chiều:** nếu budget được chọn SAU KHI thấy menu hoặc yêu cầu xác suất cover đồng thời MỌI budget, thì với K<r xác suất thành công bằng 0. Không đổi thứ tự ∀ và probability. Khi ε≥1/(2r), menu deterministic một ranking đã đủ; không dùng công thức ceil trên nhánh đó.

**Lean:** `ranking_hits_at_most_one_critical` → `menu_hit_count` → `random_menu_lower` → `uniform_submenu_coverage` → `random_menu_exact` → `post_randomization_adversary`. Các lemma đầu gần finite combinatorics, rủi ro thấp. Nhánh risky: tolerance-dependent fractional cover cho family ngoài staircase; nếu chỉ ra LP fractional set cover generic thì novelty thấp, cần actual support-radius family có integrality gap theo ε.

**Collision:** randomized incremental optimization đã tồn tại, ví dụ [Incremental Maximization via Continuization](https://arxiv.org/abs/2305.01310). Candidate của mình là exact menu-error tradeoff và quantifier separation trên scalar support geometry, không phải “randomized ranking” nói chung.

**N3. Support — giá của adaptivity và số vòng query**

Khác gói trước: gói trước kiểm adaptive sequential depth; gói này tính nonadaptive/batched depth để biết tốc độ có đến từ adaptivity không. Giữ cyclic windows length L≥1, hidden W size s≥1, m>sL; decision safe iff window tránh W. Queries là point membership, không đổi primitive.

**Đích nonadaptive:**
\[
 D_{\rm nonadaptive}(m,s,L)=sL.
\]

Upper: query toàn bộ s block rời nhau dài L. Nếu block nào toàn NO thì chọn nó; nếu mỗi block có YES thì đã quan sát đủ s holes và có thể chọn window không hole vì m>sL.

Lower, không chỉ counting m:

1. Giả sử queried set Q có |Q|<sL. Có điểm ngoài Q nên cắt cycle ở đó. Family các length-L windows nằm trọn Q trở thành line intervals.
2. Greedy chọn interval có right endpoint nhỏ nhất, đặt hit tại endpoint, xóa intervals bị hit. Chứng minh số hits bằng số disjoint witness intervals. Vì |Q|<sL, có hitting set Y⊆Q với |Y|≤s−1.
3. Trả YES trên Y, NO trên Q\Y. Mọi window nằm trong Q bị Y hit, nên không thể certify safe bằng toàn NO.
4. Cần chứng minh transcript này consistent: Y∪Qᶜ hit MỌI cyclic window. Mỗi point hit L windows, nên |Y|+|Qᶜ|≥ceil(m/L)≥s+1. Do đó có đủ unknown points để điền một W size s chứa Y.
5. Với bất kỳ proposed window: nếu có Y thì đã unsafe; nếu không, nó phải chứa một unknown point x. Điền W chứa Y∪{x}. Vậy không output nào safe cho mọi consistent world.

**Lean:** trước viết interval greedy packing/hitting lemma trên line; sau đó `nonadaptive_transcript_ambiguous` và `nonadaptive_exact`. Mục 4 bắt buộc, nếu bỏ có thể dùng một transcript không tương ứng world nào.

**Nhánh risky mới:** D_b = query complexity với tối đa b batches. Viết recurrence trên posterior finite family C:
\[
 D_b(C)=\min_Q\left\{|Q|+\max_{y:\ C_{Q,y}\ne\varnothing}D_{b-1}(C_{Q,y})\right\},
\]
D_0(C)=0 nếu có common safe action, +∞ nếu không. Đây là DP exact để tìm conjecture cho b=1,2,3. Batch Q phải được chọn trước khi thấy replies trong batch. Đừng dùng adaptive single-query policy rồi gọi nó hai-round.

Nếu adaptive exact H cũ được đóng, adaptivity gain sL/H≤2; tức cyclic family KHÔNG thể cho separation vô hạn. Muốn hướng đột phá hơn hãy thử heterogeneous tent amplitudes/holes nhưng vẫn physical geometry; hãy tìm lower + upper, không chỉ một DP table.

**Collision:** [Adaptive Submodular Ranking and Routing](https://arxiv.org/abs/1606.01530) đã nghiên cứu adaptive covering/decision tasks. [Optimal Decision Tree and Adaptive Submodular Ranking with Noisy Outcomes](https://www.jmlr.org/beta/papers/v25/23-1484.html) còn có noise, kể cả persistent noise. Vì vậy thêm noise vào API không đủ novelty; exact kernel-specific adaptivity/round tradeoff mới là câu hỏi riêng cần kiểm tiếp.

**N4. D6 — complexity của quyết định ε-tốt có thể nhỏ hơn complexity học A**

Đây là task MỚI, không phải hoàn tất Γ_label đang dang dở. Dùng corner-reference construction của `LeanD6ThresholdConstructionV1`, μ∈[0,1], q≥2, valid labels A,B. Theorem `actual_regret` đã cho, với output S=Bᶜ:
\[
 \operatorname{Regret}(A,B^c)=\frac{2-\mu}{2}|A\setminus B|.
\]

Do đó ε-good labels là exchange ball:
\[
 \mathcal B_\varepsilon(A,\mu)
 =\{B:|A\setminus B|\le\lfloor2\varepsilon/(2-\mu)\rfloor\}.
\]
Với ε<(2−μ)/2, đây vẫn là singleton A. Với radius chuẩn hóa bởi k=q+1 và tolerance ε_norm cố định, số lỗi exchange được phép là floor(2k ε_norm/(2−μ)), có thể tăng tuyến tính theo q. Đây là lý do theorem phải phân biệt exact recovery và approximate geometry.

**Đích thông tin đúng:** với θ=(A,μ),
\[
 \Gamma_\varepsilon(\theta)=
 \max_{B\in\mathcal B_\varepsilon(\theta)}\sup_w
 \inf_{\theta'=(A',\nu):\ (2-\nu)|A'\setminus B|/2>\varepsilon}
 \sum_e w_e\,\mathrm{KL}(P_{\theta,e},P_{\theta',e}).
\]

Trong theorem thông tin đầu tiên, giới hạn 0≤ε<q để mỗi answer còn có bad alternative. Nếu mở tới tolerance lớn khiến bad set rỗng, phải tách case zero-query hoặc dùng inf empty=+∞ trên extended reals; không dùng `sInf` của tập rỗng trên ℝ rồi hiểu nó là +∞. Alternative sai phải dùng ν của alternative, không dùng μ thật. Boundaries có strict >; không thay nó bằng ≥ nếu chưa chứng minh inf closure bằng nhau. Chỉ cần prove Γε≥Γ0 trước: chọn B=A, bad set cho ε là subset bad set exact.

**Đường chứng minh cụ thể:** `complement_regret_exchange` từ actual_regret và Finset.inter_compl; `epsilon_good_iff_exchange_ball`; `low_tolerance_same_answer`; `approx_bad_nuisance_intervals`. Với B cố định, enumerate exchange distance d'=|A'\B|. Bad condition tương đương ν<2−2ε/d' khi d'>0; giao với [0,1]. Nuisance objective vẫn quadratic nhưng interval endpoint phụ thuộc d'. Dùng quadratic evaluator hiện có, thêm lemma inf trên open interval bằng inf closure khi interval có interior và objective continuous. Sau đó tối ưu finite label shells.

**Experiment được giao, chưa chạy:** q=3,4,5; nhiều ε quanh (2−μ)d/2; so Γε/Γ0 và output shell. Dùng tất cả legal queries ở nhỏ q, không lấy oracle biết A làm policy. Nhánh risky: tìm regime q tăng mà recovery A tốn Θ(q) còn ε-good decision ít hơn một bậc. Nếu chỉ Γε=Γ0 ở mọi cell đã kiểm thì report negative, không tự suy ra general equality.

**Collision trực tiếp:** [Degenne–Koolen, Pure Exploration with Multiple Correct Answers](https://arxiv.org/abs/1902.03475) đã có framework và asymptotically optimal Sticky Track-and-Stop. Không gọi outer max over answers là novelty. Candidate là closed-form/phase law của exchange-ball geometric answers trong D6, nhất là normalized tolerance + growing q.

**N5. Query — thay exact key equality bằng độ bền đối với độ phân giải đo**

Khác exact-fiber repair gói cũ. Bài toán quan sát thực là y=R(θ)+e, ||e||∞≤η. World finite, scalar target g. Đề xuất theorem exact:
\[
 \mathcal E_\eta^*=
 \inf_\psi\sup_{\theta,\|e\|_\infty\le\eta}|\psi(R(\theta)+e)-g(\theta)|
 =\tfrac12\max_{\theta,\theta':\|R(\theta)-R(\theta')\|_\infty\le2\eta}
       |g(\theta)-g(\theta')|.
\]

Proof lower: hai infinity-balls overlap khi centers cách≤2η, chọn observation midpoint và dùng triangle. Upper: tại mỗi y, lấy midpoint min/max g trên compatible worlds; mọi cặp compatible có response distance≤2η. Θ nonempty, η≥0; observation không compatible world nào không thuộc supremum thực nên decoder có thể trả bất kỳ giá trị.

Từ đó định nghĩa robustness radius cho ε:
\[
 \eta_\varepsilon^{\rm crit}=
 \tfrac12\min_{|g(\theta)-g(\theta')|>2\varepsilon}
                 \|R(\theta)-R(\theta')\|_\infty.
\]
Nếu bad pairs không rỗng, guarantee đúng với η<ηcrit; ở equality cặp đạt min làm guarantee thất bại. Nếu không có bad pair thì tolerance đã đủ không cần representation; tách case này thay vì min empty trên ℝ.

**Lean:** `linfty_balls_intersect_iff` → `noisy_fiber_midpoint` → `resolution_minimax_exact` → `critical_resolution`. Không nhét ID/world-index vào R. Feature phải là response thật có đơn vị đo/noise scale; rescale coordinate tùy ý sẽ đổi ηcrit, nên normalize bằng known measurement accuracy η_l hoặc weighted infinity norm.

**Evidence mới:** dùng TOÀN panel đã collect, không lọc target hằng; dựng curve η↦floor và tỷ lệ ε-certifiable. Những exact keys độc nhất có ηcrit gần 0 thì claim sufficiency rất mong manh. Chọn η từ resolution/noise thực trước khi nhìn target outcome. Với continuous physical family, tìm nearly-null response direction G: maximize |g'(G)| subject ||R'(G)||∞≤1 và constraint δ_box/norm thật. Cái này kiểm robustness ngoài bảng finite.

**Collision:** modulus of continuity/optimal recovery là framework cũ, xem [Donoho, Statistical Estimation and Optimal Recovery](https://web.stanford.edu/dept/statistics/cgi-bin/donoho/wp-content/uploads/2018/08/SEOR.pdf). Novelty không ở midpoint identity; phải nằm ở physical nearly-null directions hoặc sharp resolution law cho representation/query trong repo. Nếu chỉ thêm η vào dataframe, coi đó là validation, không phải theorem đột phá.

**N6. MASTER — calibration không biết có thể triệt hết information của query mới**

Khác acquisition trước: trước noise centered với calibration biết; nay thêm unknown common instrument offset b. Mô hình query e:
\[
 Y_e\sim N(m_\theta(e)+b v_e,\sigma_e^2),\quad b\in\mathbb R.
\]
Hai world cho mean difference d_e. Với α_e=w_e/σ_e², profile nuisance offset khác nhau giữa hypotheses:
\[
 I_{\rm prof}(w)=\frac12\inf_u\sum_e\alpha_e(d_e-u v_e)^2
 =\frac12\left[\sum_e\alpha_ed_e^2-
 \frac{(\sum_e\alpha_ed_ev_e)^2}{\sum_e\alpha_ev_e^2}\right],
\]
khi denominator>0. Denominator=0 thì v=0 trên sampled support, profile penalty=0 và information=Σαd²/2; không xử lý bằng chia 0 cho tiện.

Proof chỉ cần complete square. Immediate negative result: v_e=1 và chỉ đo một query type thì information=0, dù d_e≠0. Lặp query vô hạn không phân biệt world với thay đổi b.

**Construction hai channel:** một control có d0=0 và một shifted-reference query có d1=γ, với γ=(1−t)^(2k−2)−(1−t0)^(2k−2) từ compensated world ĐÃ CỐ ĐỊNH. Cost/query κ0,κ1>0; raw exposure x0,x1 theo đơn vị ngân sách thỏa κ0x0+κ1x1=1. Đích:
\[
 \max_x I_{\rm prof}(x)
 =\frac{\gamma^2}{2(\sigma_0\sqrt{\kappa_0}+\sigma_1\sqrt{\kappa_1})^2},
\]
\[
 x_i^*=\frac{\sigma_i/\sqrt{\kappa_i}}{
              \sigma_0\sqrt{\kappa_0}+\sigma_1\sqrt{\kappa_1}}.
\]
Dùng Cauchy để minimize σ0²/x0+σ1²/x1. Equal σ/cost cho γ²/(8σ²), so known-offset one-channel γ²/(2σ²): penalty 4 CHỈ CHO so sánh hai design này.

**Không được quảng bá penalty 4 là universal.** Nếu có hai queries với differences +γ và −γ, allocation 1/2 mỗi query cho Σαdv=0, nuisance penalty bằng 0. Trong D6, swap hai hidden coordinates có thể tạo chính cặp dấu đối nhau. Bước nghiên cứu đáng giá là tìm tất cả legal contrast designs khử nuisance mà không biết A, rồi hỏi calibration có còn tốn thêm không. Một reference-control query có thể là thiết kế kém hơn hai spatial contrasts.

**Lean:** `profile_common_bias_square` → `single_channel_unidentifiable` → `two_channel_cost_optimum` → `balanced_contrast_no_penalty` → bridge actual response slopes. Phần algebra làm trước probability. Nhánh risky: nhiều nuisance directions v_e∈ℝ^p, projected KL bằng Schur complement; phải xử lý singular information matrix, và tìm số control directions tối thiểu với legal D6 query family.

**Collision:** Neyman/optimal cost allocation là cũ, xem [Statistics Canada, Survey Methods and Practices](https://www150.statcan.gc.ca/n1/pub/12-587-x/12-587-x2003001-eng.pdf). Structured misspecification cũng đã có matching sample-complexity work: [Réda–Tirinzoni–Degenne 2021](https://proceedings.neurips.cc/paper/2021/hash/d5fcc35c94879a4afad61cacca56192c-Abstract.html). Candidate riêng là actual reference/control/spatial contrast geometry và khi nào unknown calibration phá hoặc không phá acquisition advantage, không phải Schur complement nói chung.

**Giao người và thứ tự**

| Gói | Sản phẩm đầu tiên đủ kiểm | Rủi ro | Giá trị nếu thành công |
|---|---|---|---|
| N1 | One-cell lower và exact flat-outsider Γ_K | Thấp–vừa | Luật action complexity, test starvation có đại lượng chuẩn |
| N2 | Finite expectation lower r(1−δ)≤K | Thấp | Khóa claim randomization, exact tradeoff cho staircase |
| N3 | Nonadaptive depth=sL, gồm consistent completion | Vừa | Định lượng phần gain thật đến từ adaptivity |
| N4 | ε-good iff exchange ball; clipped nuisance bad sets | Vừa–cao | Có thể đổi bài toán từ label recovery sang geometry thực dụng |
| N5 | Resolution minimax và curve trên panel đầy đủ | Thấp phần finite, cao phần continuous | Bác hoặc củng cố transfer với noise thực |
| N6 | Profile nuisance identity và balanced-contrast test | Vừa, cao khi all hidden A | Kiểm benchmark calibration, mở design mới có chi phí rõ |

Ưu tiên nghiên cứu mới N4 và N6; ưu tiên proof dễ khóa N1 và N2. N3/N5 là cách kiểm claim hiện tại có sống dưới thay đổi thông tin hay không. Không có hướng nào được bảo đảm “chưa ai làm”; các collision gần đã dẫn cụ thể. Tám gói cũ vẫn là workstream riêng đang mở, batch này không thay thế các nghĩa vụ scheduler/termination/Gamma.
