# Batch nghiên cứu giai đoạn tiếp theo — câu hỏi mới, không phải việc tồn đọng

Ngày 2026-09-13. Chỉ hướng dẫn nghiên cứu; lượt này không khởi chạy worker, Lean hoặc experiment. Những đẳng thức mới bên dưới là derivation/to-be-formalized, không được ghi PROVED trước compile/audit. Không giao lại D04–D07, scheduler, termination, Gamma, full-extrema oracle hay sáu N1–N6 trong NEXT_BATCH_DISTINCT_DIRECTIONS_20260913.md.

Đề nghị năm gói độc lập, bao phủ sáu paper. Không phải cả năm có cùng triển vọng novelty: R1/R2 là hướng đổi mô hình đáng đầu tư; R3 có kết quả đầu dễ kiểm và câu hỏi rộng risky; R4 là ranh giới thống kê quan trọng nhưng prior rất gần; R5 có collision rõ và chỉ nên dùng làm phép thử cho một định lý về cấu trúc rộng hơn.

## R1 — Functional: thiết kế đồ thị phép đo, thay vì chỉ phân bổ mẫu vào cell

### Mô hình mới

Một relation có K>=2 action, mean theta_a và capacity C(theta)=max theta-min theta. Cho phép query một cặp e={a,b}:
Y_e ~ N(theta_a-theta_b, sigma_e^2).
Mỗi lần query có cost kappa_e>0. Đây là primitive MỚI, không được áp kết quả vào panel v4 chỉ quan sát scalar. Nếu contrast được tạo bằng trừ hai mẫu độc lập unit variance thì variance=2 và cost là hai mẫu; nếu dùng paired simulation/shared noise thì phải đo covariance thực.

Với exposure x_e>=0 trên một đơn vị budget, sum kappa_e*x_e<=1, đặt c_e=x_e/sigma_e^2. KL energy của perturbation d=lambda-theta là
E_c(d)=1/2 sum_{a<b} c_ab*(d_a-d_b)^2 = 1/2 d^T L_c d.
L_c là weighted Laplacian. Translation của tất cả action không đổi capacity lẫn observations.

### Kết quả mở đầu có thể chứng minh hoàn toàn

Lấy theta=0 và một benchmark capacity Delta>0 đã biết. Alternative là C(lambda)>=Delta. Định nghĩa J_c=inf_alt E_c(lambda).

1. Nếu positive-weight graph disconnected thì J_c=0: đặt lambda hằng trên mỗi connected component, chọn hai hằng cách nhau Delta. Mọi measured difference giữ nguyên.
2. Nếu graph connected:
   J_c=Delta^2/[2 max_{a!=b} R_eff,c(a,b)].
   R_eff là effective resistance. Chứng minh range>=Delta tương đương tồn tại ordered pair với lambda_a-lambda_b>=Delta. Với c_ab vector e_a-e_b, giải Lp=c_ab trên không gian zero-sum, R=c_ab^T p>0. Decompose lambda=(Delta/R)p+h với c_ab^T h=0 ở boundary; energy=Delta^2/(2R)+h^TLh/2. Với inequality >Delta, scaling giảm về boundary. Lấy min trên finite pairs.
3. Unit variance, unit edge cost, sum c_e=1, và được chọn mọi edge:
   sup_c J_c=Delta^2/[2(K-1)].
   Uniform complete graph c_ab=2/[K(K-1)] đạt đẳng thức.
   Không cần bắt đầu Lean bằng pseudoinverse: J_c concave theo c vì là infimum các linear functions; average c qua permutations không làm giảm J. Với uniform c dùng
   sum_{a<b}(z_a-z_b)^2=K*sum_a(z_a-mean z)^2,
   sum_a(z_a-mean z)^2 >= (max z-min z)^2/2.
   Equality witness: hai entries +/-Delta/2, các entries còn lại 0.

Ba topology với uniform edge weights, cùng total exposure:
- Complete: J=Delta^2/[2(K-1)].
- Star, K>=3: J=Delta^2/[4(K-1)].
- Path: J=Delta^2/[2(K-1)^2].
Do đó complete/path ratio=K-1. Đây là comparison trong contrast model đã khai báo, không phải speedup so với scalar panel.

### Phần nghiên cứu thực sự

Mở sang Top-k giữa nhiều relation, mỗi relation có graph riêng, extrema unknown. Với region hi_r,lo_r, các constraints lambda_hi>=lambda_a>=lambda_lo cùng capacity-flip đều tuyến tính, nhưng objective là sum Laplacian energies. Tối ưu toàn bộ region union bằng QP có certificate. Câu hỏi mới: graph tối ưu có phải đồ thị robust cho mọi pair, hay graph đổi topology khi alternative đổi extrema? Có regime mà dùng graph cố định mất một bậc theo K không?

Không assume sparse design thắng: nhiều query types hơn có thể không đáng nếu setup/cost phụ thuộc edge. Nhánh risky: kappa_ab=1+ell*|a-b| hoặc kappa_ab=|a-b|^alpha; tìm transition giữa local edges và long contrasts, so actual physical execution cost.

### Handoff thực thi

- File Lean mới dự kiến: work/p13_conjectures/LeanFunctionalContrastDesignV1.lean.
- Đọc LeanFunctionalPairFlipCostV1 để reuse square completion, nhưng v,w bây giờ là effective contrast variances; không ghi đè diễn giải module cũ.
- Viết theo thứ tự contrast_energy_nonneg, disconnected_zero_information, complete_energy_identity, complete_flat_range_cost, permutation_average_optimal. Sau đó mới general resistance bridge.
- Probe mới dự kiến: scripts/probe_functional_contrast_design_v1.py. K=3,4,6,8,12; grounded rational Laplacian trên path/star/complete. Trả potential, residual Lp-c, primal energy, dual bound và gap; không chỉ báo optimizer success.
- Tách hai output: exact flat benchmark và numerical unknown-extrema Top-k. Có thể bác hướng nếu mọi gain biến mất khi charge đủ hai cells/covariance, hoặc full oracle không tạo topology phenomenon ngoài standard linear design.

### Prior/collision

Linear experimental design và BAI đã có từ Soare–Lazaric–Munos (2014): https://proceedings.neurips.cc/paper_files/paper/2014/file/f8d84caae48546d0934d637ab54f7086-Paper.pdf . Dirichlet energy/effective resistance là công cụ chuẩn. Candidate riêng là measurement-graph design cho RANGE với extrema thay đổi, một luật topology theo K và cost thực. Ba công thức flat riêng lẻ chưa đủ để gọi là breakthrough.

## R2 — D6: hai mục tiêu học có thể cần hai độ rộng query trái ngược

### Mô hình và công thức cần chứng minh

Giữ actual world/query means trong repo. Width r query có cost kappa(r)>0 và variance v(r)>0. Restricted width envelope đầu tiên: 2<=r<=q, h=false, G subset B=others A j và |G|=r. Cardinality r>=2 là legality thật; không kéo công thức này xuống r=1.

Gọi a(mu)=1-mu. Hai quantities KHÁC NHAU:
- KL trung bình trên q(q+1) adjacent label swaps tại cùng mu, chia query cost:
  I_label_avg(r)=a(mu)^2*r/[2*q*v(r)*kappa(r)].
- KL phân biệt mu và nu khi A đã biết, cùng query G:
  I_margin(r)=(mu-nu)^2*r^2/[2*v(r)*kappa(r)].

Đường proof label: actual_fixed_margin_sum, thay |G intersect A|=0, |G intersect B|=r. actual_average_width_bound cho upper với mọi G cùng width; G subset B đạt upper. Đường proof margin: actual_mean_affine cho mean=1+r-r*mu, nên mean difference=-r*(mu-nu); dùng equal-variance Gaussian KL.

Đây là ORACLE WIDTH ENVELOPES: equality witness G subset B biết A, và label quantity là average tại same mu, không phải minimax profile over nuisance. Không viết chúng thành adaptive Gamma.

Nếu kappa(r)=r^alpha, v(r)=sigma0^2*r^beta, z=alpha+beta:
I_label_avg proportional r^(1-z), I_margin proportional r^(2-z).
Với nonzero signal:
- z<1: cả hai envelope thích width lớn.
- 1<z<2: label-average thích width nhỏ, known-A margin thích width lớn.
- z>2: cả hai thích width nhỏ.
Tại z=1, label-average phẳng theo r; tại z=2, known-A margin phẳng theo r.

### Kết quả nghiên cứu đích

Với x_e là số lần đo trên một đơn vị cost:
Gamma_c(theta)=sup_{x>=0,sum kappa_e*x_e<=1} inf_{theta' in Alt(theta)} sum_e x_e*(m_theta(e)-m_theta'(e))^2/(2*v_e).

Hỏi vùng 1<alpha+beta<2 có thực sự buộc optimal design dùng đồng thời ít nhất hai widths không; ranh giới đó phụ thuộc q, mu ra sao? Đây là câu hỏi mới về thiết kế measurement, độc lập với việc ghép scheduler đang mở.

Không conjecture mixture là luôn cần: full game có thể cho một width trung gian hoặc same-margin dual quá lỏng. Cả hai là kết quả giúp chỉnh hướng.

### Cách làm cụ thể

- Lemmas đầu làm trên arrays positive cost/variance; so r/[kappa*v] và r^2/[kappa*v]. Tránh vướng Real.rpow trước khi chứng minh finite-width law.
- Module dự kiến LeanD6WidthCostPhaseV1.lean; imports LeanD6QueryWidthInformationV1 và LeanD6GaussianQueryDominanceV1.
- Solver q=3,4 trước. Include mọi legal G của allowed widths, không chỉ G subset true B. Fix true A để evaluate instance; policy optimization vẫn nhìn toàn bộ query family.
- Với mỗi alternative A', m_A',nu(e)=a'_e*nu+b'_e, nuisance objective là quadratic. Nếu H=sum x_e*a'_e^2/v_e>0, minimizer nu*=clip(sum x_e*a'_e*(m_theta(e)-b'_e)/v_e / H) lên domain nuisance thật. H=0 xử lý constant objective, không chia 0.
- Solve design bằng exchange/cutting-plane, kiểm lower/upper certificate. Lưới z=0,0.5,1,1.25,1.5,1.75,2,2.5 và mu quanh biên pha hiện có. Report histogram mass theo width và dual active alternatives.
- Cost physical checks: independent summed noise có beta=1; nếu work tuyến tính theo r thì alpha=1. Khi đó z=2, lợi thế r^2 trên đơn vị query có thể thành width-neutral trên đơn vị work.

### Prior/collision

Cost/resource-constrained BAI đã có: Li–Cheung, Best Arm Identification with Resource Constraints (AISTATS 2024), https://proceedings.mlr.press/v238/li24c/li24c.pdf . Chia KL cho cost không mới. Candidate là hai critical exponents và actual D6 composite-game phase law; elementary envelopes chỉ là lemma khởi động.

## R3 — Structural: giá sửa quyết định khi budget đổi, không phải thêm ranking vào menu

Đặt p_i=(i,false), n_t=(t,true), U=StairRel r,
B_t={n_t} union {p_i:i<=t}, S_t=U minus B_t, k_t=2r-t-2.
Đây đúng staircaseBlock/staircaseSelected trong LeanStructuralStaircaseFamilyV1.

Giữa hai retained sets S,T, định nghĩa excess deletion
rec(S,T)=|S minus T|-max(0,|S|-|T|).
Số trừ phía sau là deletion bắt buộc vì budget giảm; rec đo thay thế THÊM. Không gọi rec là toàn bộ chi phí thực: insertion/deletion phải được báo riêng nếu deployment charge cả hai.

### Theorem đích đầu

Với t!=u:
- Nếu t>u (budget tăng), S_t minus S_u={n_u}; số deletion=1.
- Nếu t<u (budget giảm), S_t minus S_u={n_u} union {p_i:t<i<=u}; số deletion=u-t+1, trong đó u-t bắt buộc.
Suy ra rec(S_t,S_u)=1 ở cả hai chiều.

Với normalized tolerance 0<=eps<1/(2r), unique critical-budget optimum buộc mọi epsilon-good policy chọn S_t. Cho bất kỳ sequence critical indices t_0,...,t_T, minimum total excess recourse = number of index changes, EXACT, kể cả budget nhảy nhiều hoặc quay lại. Theo chiều budget tăng tuần tự, total deletions=r-1, max deletion mỗi bước=1. Không phải Theta(r^2).

Ghép với chi_eps=r: menu complexity tăng không giới hạn theo r trên diagonal tolerance này, nhưng một replacement mỗi lần đổi critical budget là đủ. Chỉ theorem trên critical-budget window; không tự mở sang mọi budget.

### Proof/Lean

- File dự kiến LeanStructuralBudgetRecourseV1.lean.
- Đọc staircaseBlock, staircaseSelected, staircaseSelected_unique_optimal; normalized_epsilon_exact trong LeanStructuralStaircaseToleranceLowerV1.
- Prove membership set-difference trước; đếm Finset.Ioc cardinality sau. Tách t<u/t=u/t>u.
- Prove selected_transition_recourse, epsilon_policy_forced_at_critical, path_recourse_exact bằng Finset.sum equality. Không cần probability.

### Câu hỏi risky mạnh hơn

Với arbitrary normalized scalar support model sum_i osc(f_i)/2=1, define
R_eps(f)=min_{S_0,...,S_m epsilon-good at each budget} max_{k<m}|S_k minus S_{k+1}|.
Tại eps>0 cố định, R_eps có uniform bound chỉ theo eps không, hay có family R_eps->infinity? Đây chưa phải theorem; chưa chốt hằng số C/eps.

Cách tìm: finite support matrices m=6,8,10, compute EXACT radius của mọi subset, F_k={S:|S|=k, radius(S)<=opt_k+eps}. DP:
D_0(empty)=0;
D_{k+1}(T)=min_{S in F_k} max(D_k(S), |S minus T|).
Terminal min D_m cho đúng R_eps. Dùng rational matrices/eps để ties không đổi vì float. Khác biệt với menu: cùng một path được phép thay set, không bị buộc nested.
Nếu tìm large R_eps, trích witness hai/nhiều layers và dual/cut certificate, rồi mới xây parametric family. Nếu luôn nhỏ, thử xây rolling replacement path từ approximate anchors; phải duy trì epsilon-good tại CÁC budget trung gian, không chỉ anchors.

### Prior/collision

Recourse không mới: https://arxiv.org/abs/1312.4075 . Không bán tên gọi mới. Candidate là exact separation menu/recourse trên actual normalized support geometry và, nếu có, universal law tại eps cố định. So sánh chuẩn additive error và changing cardinality; không đồng nhất với multiplicative submodular guarantees.

## R4 — Support: passive sampling có chứng nhận được geometry hay không?

Đổi acquisition từ hỏi membership chủ động sang quan sát i.i.d. point trên support. Geometry và selectedRadius giữ nguyên. Đây là bài toán thống kê mới, không phải hoàn tất U03.

### Kết quả âm cần chứng minh trước

Dùng m=2 trong LeanSupportMultiTipGeometryV1, retained decision j in {0,1}. P0=delta_anchor. Với j in {0,1}, eta>0:
P_{j,eta}=(1-eta)*delta_anchor+eta*delta_tip(j).
P0 có cả hai decision radius=0. P_{j,eta} có selectedRadius({j})=1/2 và decision kia radius=0, không phụ thuộc eta.

Đích: với eps<1/2, delta<1/2, không tồn tại passive algorithm uniformly delta-correct trên family {P0,P_{j,eta}:j=0,1,0<eta<1} mà dừng gần chắc chắn tại P0 và trả retained singleton. Cho phép randomized algorithm.

Proof không cần KL/Pinsker:
1. Dưới P0 mọi observation là anchor. Có output j với probability>=1/2.
2. Vì tau finite a.s., chọn N sao cho a=P0(tau<=N, output=j)>delta.
3. Chọn eta nhỏ sao cho (1-eta)^N*a>delta.
4. Couple internal randomization giữa P0 và P_{j,eta}. Khi N observations đều anchor, thuật toán có cùng transcript. Do đó error dưới alternative ít nhất (1-eta)^N*a>delta.

Không ghi “không thể học support” chung chung: điều không thể ở đây là trả một epsilon-safe decision, dù P0 bản thân có TẤT CẢ decisions an toàn. Nếu cho phép abstain mãi tại P0 thì theorem không áp dụng; termination ở P0 là giả thiết thiết yếu.

### Positive family và công thức đối chiếu

Với m>=2, dense family W_w=univ minus {w},
P_w=rho*delta_anchor+(1-rho)/(m-1)*sum_{u!=w}delta_tip(u), 0<rho<1.
Chỉ decision w có zero radius. Uniform masses/rho known. Optimal ZERO-ERROR passive stopping time cần và đủ thấy hết m-1 present tips:
E[tau]=(m-1)*H_{m-1}/(1-rho).
Membership depth đã có là m-1. Ratio passive expectation / active worst depth=H_{m-1}/(1-rho); ghi rõ hai tiêu chí chi phí khác nhau.

Lower: finite prefix còn ít nhất hai unseen indices thì cùng prefix có positive probability dưới ít nhất hai incompatible worlds; zero-error rule không được stop. Upper: khi đủ m-1 tips, output index còn lại. Expected time: sau k distinct tips, new-tip probability=(1-rho)*(m-1-k)/(m-1); cộng mean waiting time của m-1 geometric stages.

### Handoff

- LeanSupportPassiveCertificationV1.lean dự kiến. Bắt đầu finite-N coupling inequality + radius_formula. Infinite stopping impossibility chỉ cần continuity of increasing events; không formalize coupon process trước.
- Ràng buộc của positive theorem: family biết chính xác m-1 tips, positive uniform mass. Nếu bỏ cardinality information, rule “đợi m-1 tips” có thể không terminate.
- Numerical evidence chỉ để minh họa: m=4,8,16,32 và rho=0.1,0.5; kiểm mean với analytic variance/CI, không dùng Monte Carlo để thay theorem.
- Research tiếp: minimal probabilistic regularity bảo đảm expected-time certificate với positive eps; lower bound vào mass của các UNSAFE-relevant regions, không nhất thiết minimum mass của mọi tip. Tìm family có nhiều rare irrelevant tips nhưng few dangerous tips để tách hai quantities. Đây là đích mới có triển vọng hơn coupon formula.

### Prior/collision

Minimum-mass assumptions trong unseen/support estimation đã có: Wu–Yang, https://arxiv.org/abs/1504.01227 . Coupon collector và rare-event impossibility không mới. Candidate riêng: necessary/sufficient mass condition chỉ cho decision-relevant geometry, yếu hơn full-support recovery. Đừng định vị standalone coupon theorem là novelty.

## R5 — Query + MASTER: evidence có thể chỉ đáng tiền khi mua cả bundle

Đây là hướng risky để kiểm giới hạn của myopic acquisition, không phải thêm scheduler hoặc sửa exact-fiber decoder.

### Construction trên support thật

d>=2, m=d+2. World x in {0,1}^d, b(x)=XOR x_i. Dùng multi-tip support với
W_x={1-b(x)} union {i+2:x_i=1}.
FEASIBLE retained decisions của task này chỉ là j=0,1. Đây là restriction của mô hình mới và phải ghi rõ; nếu cho phép chọn auxiliary j, safe decision có thể lộ quá sớm và theorem không đúng.

radius_formula cho normalized decision loss
ell(x,j)=2/(m-1)*selectedRadius(components W_x,{j})=1[j!=b(x)].
Physical membership at tip(i+2) đọc bit x_i, cost=1. Membership at either tip0/tip1 đọc parity, cost=M>0. Không cấm direct query; charge cost rõ.

Uniform prior trên x, noiseless queries, hard pathwise budget B. Bayes error optimum:
R*(B)=1/2 nếu B<min(d,M), và 0 nếu B>=min(d,M).
Zero-error minimum cost=min(d,M).
Proof lower adaptive: khi chưa query direct và còn một bit chưa biết, conditioned on ANY realized transcript, completions pair bijectively bằng flip một unqueried bit. Parity vẫn uniform. Proof upper: hỏi d bits hoặc một direct query.

Với M>d, greedy chỉ tối đa hóa one-step expected risk reduction / cost sẽ chọn direct query vì mỗi bit có gain 0, direct có gain 1/(2M)>0. Overpayment M/d không bị chặn. Đây là result cho đúng greedy criterion, không phải cho mọi greedy/entropy/HEC method.

### Công việc và chỗ phải đi xa hơn

- File dự kiến LeanQueryEvidenceBundleV1.lean: actual_radius_parity_loss; partial_assignment_parity_balance; adaptive_unseen_bit_balance; hard_budget_risk_cliff; myopic_cost_ratio.
- Finite posterior DP trước: posterior states partial bit assignments, O(3^d), d=2..10, M=d,2d,d^2. So Bayes-risk greedy, posterior-world-entropy greedy, optimal bundle DP. Có negative control để entropy method KHÔNG bị gán cùng failure.
- Đích nghiên cứu vượt witness: characterize actual geometry/query classes mà Bayes-risk gain có bounded complementarity order hoặc có sound bundle surrogate. Kiểm laminar unsafe sets / interval membership làm restricted class, không phát biểu universal submodularity.
- Nếu thử noisy bits, hãy đọc noisy decision-tree prior trước. Không giao việc “prove noisy parity d log d” rồi gọi mới.

### Collision nặng, đã xác minh

Krause–Guestrin (UAI 2005) đã dùng XOR để chứng minh information gain không submodular nói chung: https://www.cs.cmu.edu/~guestrin/Publications/UAI2005/uai2005.pdf . Noisy parity đã được Feige–Raghavan–Peleg–Upfal (1994) nghiên cứu: https://epubs.siam.org/doi/abs/10.1137/S0097539791195877 ; còn có unified noisy-query lower-bound paper 2026: https://arxiv.org/abs/2606.11448 . Vì vậy witness trên là stress test/realization lemma, KHÔNG phải headline novelty. Chỉ đầu tư tiếp nếu xác định được physical restricted class + sharp positive bundle guarantee mà framework DRD/HEC chưa cho cùng phát biểu.

## Thứ tự giao và điều kiện nghiệm thu

Giao độc lập R1, R2, R3 trước; R4 ưu tiên theorem mass condition hơn mở rộng census; R5 là nhánh high-risk có stop rule theo collision.

Mỗi worker phải trả bốn thứ cụ thể:
1. Model contract: giữ/thay observation primitive, feasible decisions, cost/noise và quantifiers nào.
2. Một derivation hoặc phản ví dụ exact cho target, với actual geometry/means bridge.
3. Claim mới so với named prior ở cùng model; nếu chỉ corollary thì nói rõ.
4. Source + compile exit + axiom audit cho theorem đã formalize; numerical artifact có producer/config và primal/dual hoặc paired evidence phù hợp.

Không nghiệm thu bằng số module. Không có package nào ở đây đòi chờ full adaptive Gamma đang mở. Các tên module/probe ở trên là tên ĐỀ XUẤT, không phải file đã tồn tại hoặc đã được compile.
