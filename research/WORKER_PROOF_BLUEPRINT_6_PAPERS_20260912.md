# Bản giao việc chứng minh cho sáu paper

Đây là hướng dẫn nghiên cứu và formalization, dựa trên source đã đọc và literature đã tra trong lượt này. Không có module Lean, compile hoặc experiment nào được thực hiện để tạo tài liệu này. Các công thức mới dưới đây là suy luận toán trong bản hướng dẫn, chưa phải theorem đã audit. Tên lemma đánh dấu **MỚI** là tên đề nghị, không phải API đã tồn tại.

**Quyết định ưu tiên.** Giao tám gói: Functional oracle; Structural menu có anchor gần tối ưu; Support kernel–query; D6 luật reference/biên; adaptive scheduler; adaptive stopping–kỳ vọng; Query repair; MASTER acquisition. Gói 1, 3, 4 có construction/công thức cụ thể đáng thử nhất. Gói 5–6 đóng tính đúng của thuật toán; sự có mặt của Γ/GLR tự nó không tạo novelty. Gói 7 có collision trực tiếp, nên chỉ làm thành kết quả riêng nếu constraint vật lý tạo một luật vượt khỏi Test Cover. Không có kết luận “cả sáu đủ publish”.

**Quy tắc giao worker.** Mỗi gói trả bốn thứ: phát biểu với đầy đủ lượng từ; proof viết tay; file Lean và receipt nếu đã formalize; một phản ví dụ/negative control có thể làm claim thất bại. Không nhận “compile sạch” thay cho việc theorem phát biểu đúng mục tiêu. Không nhập kết luận vào field của structure rồi gọi wrapper là chứng minh. Tất cả file mới đặt trong `/Users/phanan/cig-amf-main/work/p13_conjectures/` hoặc `/Users/phanan/cig-amf-main/research/` theo loại.

**Các phần không được làm lại.** D03 response levels; S02 tolerance quantifiers; U03 sparse/dense obstruction separation đã có. D05–D06 có physical certificate dưới điều kiện `strong`; không được nói minimax còn hoàn toàn trống. Full-extrema oracle đã có proof sketch mới trong [F05 bản sửa](/Users/phanan/cig-amf-main/research/high_risk_20260910/F05_FULL_EXTREMA_ORACLE_20260912b.md); bốn tỷ số A/B/C/D của bản cũ đã bị rút. Hai nhóm adaptive mới còn nằm ở thư mục ngoài repo phải được nhận bàn giao theo hash trước khi dùng; sự có mặt của source chưa đồng nghĩa compile xong.

**1. Functional — formalize oracle thật và hai họ phá mọi so sánh hằng số với scalar proxy**

**Mục tiêu và mô hình.** Có R relation, K action, bảng mean tự do θ, Gaussian độc lập với variance biết trước. Đặt α_ra=w_ra/σ_ra²>0 và C_r(θ)=max_a θ_ra−min_a θ_ra. T là Top-k duy nhất của θ. Chi phí alternative đóng:

\[
 J_{\rm full}(\alpha,\theta)=\inf_{\lambda:\exists i\in T,j\notin T,\ C_i(\lambda)\le C_j(\lambda)}
 \frac12\sum_{r,a}\alpha_{ra}(\lambda_{ra}-\theta_{ra})^2.
\]

Đây là chi phí chạm biên tie. Với đảo thứ tự nghiêm, chứng minh bằng perturbation rằng infimum bằng nhau; không khẳng định nghiệm tie là nghiệm đảo nghiêm. Khởi đầu với α>0 để tránh vấn đề zero weights/coercivity; mở rộng α=0 là nhiệm vụ riêng.

**Theorem đích 1:**

\[
 J_{\rm full}=\min_{i\in T,j\notin T}\inf_{z\ge0}\{S_i(z)+E_j(z)\},
\]
\[
 S_i(z)=\min_{\ell\in\mathbb R}\frac12\sum_a\alpha_{ia}
           \operatorname{dist}(\theta_{ia},[\ell,\ell+z])^2,
\]
\[
 E_j(z)=\min_{a\ne b}
 \frac{[z-(\theta_{ja}-\theta_{jb})]_+^2}
 {2(1/\alpha_{ja}+1/\alpha_{jb})}.
\]

Đường chứng minh, theo đúng thứ tự:

1. `range_le_iff_interval` **MỚI**: range λ≤z iff tồn tại ℓ sao cho mọi λ_a∈[ℓ,ℓ+z]. Chiều thuận lấy ℓ=min λ. Chiều ngược dùng max/min bounds.
2. `range_ge_iff_pair` **MỚI**: range λ≥z iff có ordered pair với λ_a−λ_b≥z. Với z=0, K≥2 cho phép chọn hai chỉ số khác nhau ngay cả khi mọi cell bằng nhau.
3. `projection_interval_min` **MỚI**: nghiệm từng cell là min(ℓ+z,max(ℓ,θ_a)). Chia ba trường hợp θ_a<ℓ, nằm trong interval, θ_a>ℓ+z. Chứng minh bất đẳng thức bình phương trước, rồi `Finset.sum_le_sum`.
4. `pair_open_cost` **MỚI**: đặt g=z−(θ_a−θ_b). Nếu g≤0 giữ nguyên; nếu g>0, đặt displacement x=g/(α_a(1/α_a+1/α_b)), y=−g/(α_b(1/α_a+1/α_b)). Khi ấy x−y=g và energy đạt công thức E. Cận dưới dùng `pair_flip_lower` với v=1/α_a, w=1/α_b và biến −y.
5. `full_cost_decomposition` **MỚI**: alternative là union hữu hạn theo i,j; với mỗi alternative chọn z giữa hai capacity. Hai relation có hai block tọa độ rời nhau, nên các năng lượng cộng được; giữ mọi relation khác tại θ. Chứng minh cả lower cho mọi λ lẫn explicit witness upper trước khi thao tác với infimum.

API thực đã đọc: [LeanFunctionalPairFlipCostV1](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanFunctionalPairFlipCostV1.lean), namespace `CIGAMF.P13.FunctionalPairFlipCost`, có `energy_decomposition`, `pair_flip_lower`, `pair_flip_attained`. Nó là bài toán hai score không có ordering constraints. Phải phân biệt J_scalar, J_old (QP giữ region extrema cũ), J_full: J_scalar≤J_old và J_full≤J_old; không có thứ tự tổng quát giữa J_scalar và J_full.

**Theorem đích 2: hai witness tường minh, không cần tìm bằng optimizer.** Dùng hai relation i,j, ba action, Top-1=i, 0<η≤1. Ký hiệu α_i là vector precision, không phải xác suất allocation; mọi vector dương có thể hiện thực bằng variance thích hợp và allocation đều.

Họ A, cell giữa của j rẻ:

\[
\theta_i=(0,1,1/2),\quad\alpha_i=(1,1,1),\qquad
\theta_j=(0,1/2,1/4),\quad\alpha_j=(1,1,\eta).
\]

Capacity gap=1/2; effective variances tại extrema cũ là v_i=v_j=2. Do đó J_scalar=1/32. Chỉ đổi cell thứ ba của j từ 1/4 lên 1: capacity j thành 1, energy=9η/32. Suy ra

\[
0\le J_{\rm full}/J_{\rm scalar}\le9\eta\longrightarrow0.
\]

Họ B, max cũ rẻ nhưng runner-up đắt:

\[
\theta_i=(0,1,3/4),\quad\alpha_i=(1,\eta,1),\qquad
\theta_j=(0,1/2,1/4),\quad\alpha_j=(1,1,1).
\]

Lúc này J_scalar=η/[8(1+3η)]. Với BẤT KỲ alternative, lấy z giữa capacity i và j. Hai cell đắt 0 và 3/4 của i buộc chi phí co ít nhất [3/4−z]_+²/4. Mọi cặp cell gốc của j có chênh lệch≤1/2, nên mở range lên z tốn ít nhất [z−1/2]_+²/4. Đặt u=[3/4−z]_+, v=[z−1/2]_+; có u+v≥1/4 và u²+v²≥(u+v)²/2. Vì vậy

\[
 J_{\rm full}\ge1/128,
 \qquad J_{\rm full}/J_{\rm scalar}\ge\frac{1+3\eta}{16\eta}\longrightarrow+\infty.
\]

Worker có thể formalize hai họ TRƯỚC oracle tổng quát: `cheap_middle_feasible`, `cheap_middle_cost`, `runner_up_pair_lower`, `runner_up_uniform_lower`, `scalar_full_not_uniformly_comparable` **đều MỚI**. `norm_num` cho các vector Fin 3; `field_simp` chỉ sau chứng minh η≠0; `nlinarith [sq_nonneg (u-v)]` cho cận 1/128. Không cần `native_decide`, không cần giả thiết về nghiệm optimizer.

**Solver exact để phục vụ thuật toán.** Với active sets L={a:θ_a<ℓ}, U={a:θ_a>ℓ+z}, nghiệm interval center là

\[
\ell(z)=\frac{\sum_{a\in L}\alpha_a\theta_a+
                    \sum_{a\in U}\alpha_a(\theta_a-z)}
                   {\sum_{a\in L\cup U}\alpha_a}.
\]

Kiểm các inequalities xác định L,U; trong mỗi region, S là quadratic theo z. Denominator bằng 0 nghĩa là không cell nào bị clip, S=0; phải tách case này. Với ordered pair a,b của j cố định, S_i+E_j^{ab} là convex theo z. Liệt kê region boundaries và stationary points hợp lệ, so giá trị bằng rational khi input rational. Đó là oracle có certificate; không gọi một lần SLSQP là global proof.

**Sau oracle, allocator nào?** J(w) là infimum các hàm tuyến tính theo w nên concave. Alternative tối ưu λ* cho supergradient g_ra=(θ_ra−λ*_ra)²/(2σ_ra²): J(v)≤J(w)+g·(v−w). Nếu oracle ε-optimal thì thêm ε ở vế phải. Dùng điều này cho optimizer có gap certificate, rồi so với C_lucb trên cùng thông tin. Chưa có lý do bảo đảm thắng C_lucb; hai witness chỉ chứng minh proxy có thể sai nghiêm trọng.

**Collision và cửa đi tiếp.** Projection với range constraints thuộc một dòng least-squares cũ, ví dụ [Evans–Cantoni, A note on least-squares approximation with range constraints](https://doi.org/10.1017/S0334270000002046). Bài đó không tự chứng minh toàn bộ Top-C oracle này. [Huang et al., Structured Best Arm Identification](https://proceedings.mlr.press/v76/huang17a.html) là đối chiếu bắt buộc; assumption về tính tăng theo từng tọa độ không áp dụng trực tiếp cho range của raw cell. [Jourdan–Degenne–Kaufmann, Dealing with Unknown Variances](https://arxiv.org/abs/2210.00974) chiếm phần “unknown variance” chung. [Dorn et al., Functional multi-armed bandit and the best function identification problems](https://arxiv.org/abs/2503.00509) khiến tên “functional bandit” không thể được xem là mới.

Điểm đáng thử là định lý không so sánh được bằng hằng số + oracle toàn extrema + một lớp instance chứng minh allocator hưởng lợi. Nếu mọi đóng góp chỉ còn min theo region, novelty yếu. Nhánh rủi ro cao: giữ coupling cùng một F; khi đó phép tách block ở bước 5 có thể hỏng, phải dùng constrained quadratic oracle. Một counterexample coupling hỏng cũng là kết quả phạm vi hữu ích.

**Nghiệm thu gói 1:** hai witness có lower/upper audit; oracle equality dưới free-table scope; exact certificates cho tie/zero-gap; benchmark mới đối đầu C_lucb. Không dùng lại bốn tỷ số F05 đã rút.

**2. Structural — biến upper tồn tại thành thuật toán dùng anchor gần tối ưu**

Luật O(1/ε) không cần balanced radii đã có lõi. Phần đáng làm tiếp là hợp đồng với solver anchor không exact và số lần phải gọi solver; không formalize lại S02.

Sắp c_0≤⋯≤c_{m−1}, c_i≥osc(f_i)/2≥0, B=Σ_i c_i>0. Đặt

\[
 d_k=c_k+c_{m-1-k},\quad\Phi(k)=\sum_{u<k}d_u,\quad\Phi(m)=2B.
\]

Chọn 0≤η<ε. Oracle ở budget a trả S_a, |S_a|=a, R(S_a)≤OPT_a+ηB. Chọn bucket width h=(ε−η)B và b(k)=floor(Φ(k)/h). Mỗi bucket không rỗng chỉ gọi oracle tại budget nhỏ nhất a. Từ S_a cứ thêm phần tử rẻ nhất còn thiếu theo thứ tự c.

**Định lý đích:** menu có

\[
 |\mathcal M|\le\left\lfloor\frac{2}{\varepsilon-\eta}\right\rfloor+1,
 \qquad \forall k\le m\ \exists\pi\in\mathcal M:
 R(\pi_{\le k})\le OPT_k+\varepsilon B.
\]

Proof thật gồm ba mắt:

1. **Step lemma đã có.** `optimal_step_of_cheap` trong [OrderedRadiusStep](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanStructuralOrderedRadiusStepV1.lean) nhận epsilon tùy ý, không chỉ 0. Proof so với T tối ưu size k+1: xóa j rẻ bên trong T, dùng |R(S∪i)−R(S)|≤c_i ở hai phía. Charge d_k xuất hiện từ c_i≤c_k, c_j≤c_{m−1−k}.
2. **Induction cần mở rộng.** [OrderedRadiusChain](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanStructuralOrderedRadiusChainV1.lean) có `evolution_optimal` nhưng anchor nhận ε=0. Viết `evolution_approx_optimal` **MỚI**, giữ ηB suốt induction: error=ηB+accumulated(c,a,k−a). Copy cấu trúc induction đã có; base simp, succ gọi step lemma với error hiện tại. Cardinality vẫn dùng `evolution_card`.
3. **Bucket proof.** `accumulated_eq` của [UnbalancedToleranceUpper](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanStructuralUnbalancedToleranceUpperV1.lean) cho accumulated=Φ(k)−Φ(a). Cùng bucket và a≤k cho 0≤Φ(k)−Φ(a)<h. Cộng ηB ra εB. Viết `metric_cover_with_anchor_slack` **MỚI** bằng cách mở rộng [metric_cover](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanPrefixBudgetMetricCoverV1.lean); không cần phát minh lại floor/ceil lemmas.

**Computability là một nghĩa vụ riêng.** `next` hiện dùng Classical.choose, nên theorem tồn tại chưa phải executable algorithm. Định nghĩa `nextIndex` bằng min' của complement theo index đã sort; chứng minh nó thỏa premise `cheap_outside`, sau đó dùng cùng step theorem. Với c rational và oracle anchor hữu hạn, có thuật toán thật. Thời gian ngoài oracle có thể O(m log m+m|M|), tính cả kích thước output m|M|; phải ghi chi phí oracle riêng. Không tuyên polynomial cho solver anchor tùy ý.

**Nhánh rủi ro cao:** lower bound số oracle calls cho model chỉ thấy trả lời oracle, hoặc menu gần tối ưu từ radii ước lượng. Muốn lower oracle calls phải định nghĩa thông tin được phép xem; nếu worker được toàn F thì counting oracle calls vô nghĩa. Với radii upper bounds tổng \bar B, certificate tự nhiên là ε\bar B; muốn εB phải trả factor \bar B/B, không được âm thầm thay normalizer.

**Collision.** [Kurtz, Bounding the Optimal Number of Policies for Robust K-Adaptability](https://arxiv.org/html/2409.12630v3) có điều kiện uncertainty convex và objective continuous/concave trong uncertainty cho bound theo dimension. Budget nguyên không convex; extension bằng prefix floor cũng không continuous/concave. Vì vậy không được viết “chỉ thiếu concavity” nếu chưa đưa embedding đầy đủ. [Bienkowski et al., Incremental Submodular Maximization: Better Than Greedy](https://arxiv.org/abs/2606.28558) nghiên cứu một thứ tự cho mọi cardinality trên monotone submodular maximization. Phân biệt của mình là additive support radius có cancellation, menu nhiều ranking, và tolerance chuẩn hóa. Constructive slack theorem là phần usability của luật đã có, chưa đủ làm headline mới riêng.

**Nghiệm thu gói 2:** theorem với η, thuật toán next bằng finite minimum, oracle-call count; không giả định exact anchor. Không gọi diagonal ε_r→0 là unbounded dimension tại một ε cố định.

**3. Support — kernel geometry thật, query lower bound sửa đúng, rồi mới thử luật parity exact**

**Phải sửa một proof route ngay.** [SUPPORT_law_probe.py](/Users/phanan/cig-amf-main/scripts/SUPPORT_law_probe.py) định nghĩa H(s) bằng s cyclic intervals, chỉ s−1 interval có private point. Với m=13,L=3,s=3:

\[
 I_1=\{0,1,2\},\ I_2=\{2,3,4\},\ I_3=\{1,2,3\}.
\]

0 là private của I1, 4 là private của I2, nhưng union có 5 điểm. Công thức đang thử cho H(3)=7. Vậy helper lemma đó SAI. Đây là phản ví dụ exact từ định nghĩa, không phụ thuộc kết quả chạy script. Nó chưa bác final query-depth conjecture.

**Construction cần dựng.** Có m≥2 tọa độ và m tip, kernel φ(j,w)≥0. Đặt

\[
 \Phi_w=\sum_j\phi(j,w),\quad c_w=\Phi_w/(m-1),\quad
 P_w(j)=c_w-\phi(j,w),\quad S_W=\{0\}\cup\{P_w:w\in W\}.
\]

Khi chỉ giữ component j, residual trên tip P_w là

\[
 \sum_{i\ne j}P_w(i)=(m-1)c_w-\sum_{i\ne j}\phi(i,w)=\phi(j,w).
\]

Do có anchor 0 và kernel không âm,

\[
 R_W(\{j\})=\tfrac12\max(\{0\}\cup\{\phi(j,w):w\in W\}).
\]

Do đó safe ở tolerance ε iff W∩A_j=∅, A_j={w:φ(j,w)>2ε}. Đây là bridge selectedRadius→query game, không dùng toyRegret.

Physical membership cần P_w khác nhau và khác 0. Với kernel tùy ý điều đó KHÔNG tự đúng. Chuyên biệt cyclic tent φ(j,w)=h·max(0,R+1−dist_cycle(j,w)), h>0, m đủ lớn so với support kernel. Tổng Φ_w không phụ thuộc w và peak tại w duy nhất, nên P_w injective; có cell ngoài kernel nên tip không phải vector 0. Chứng minh các điều này trước `P_a ∈ S_W ↔ a∈W`.

Với tolerance cố định, A_j là các cyclic window cùng độ dài L=2r−1 (r là cutoff nguyên thỏa h(R+1−d)>2ε). Nếu cutoff r=0 thì D=0, tách trước. Không dùng công thức L=2r−1 với natural subtraction khi r=0.

API mẫu: [SupportMultiTipGeometry](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanSupportMultiTipGeometryV1.lean) có `residual_none`, `residual_some`, `radius_formula`, `physical_membership_iff`; chúng cho kernel cụ thể cũ, không tự là generic tent theorem. [U03](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanSupportObstructionQueryOrderV1.lean) đã đóng sparse/dense; giữ nó làm benchmark, không làm lại.

**Theorem query khả thi để nhắm trước:** hidden W có |W|=s≥1; query membership một điểm; deterministic, adaptive, zero-error, worst-case depth; m≥sL+1. Nhắm

\[
 H(s,L):=\lfloor s/2\rfloor(L+1)+(s\bmod2)L
 \ \le D(m,s,L)\le sL.
\]

Đây là proof đề xuất dưới đây, CHƯA Lean-checked. Nó đã cho matching order Θ(sL), ngay cả khi upper parity exact chưa tìm được.

**Upper sL có algorithm cụ thể.** Chọn trước s block rời nhau, mỗi block L điểm liên tiếp. Trong mỗi block query đến YES đầu tiên hoặc query hết. Nếu hết toàn NO thì trả center block: safe. Nếu s block đều cho YES thì đã biết đủ s phần tử của W; mỗi hole làm bẩn đúng L center, nên tối đa sL<m center bị bẩn, tồn tại một center safe. Chi phí≤sL. Prove bằng induction theo số block, giữ invariant các YES khác nhau và cost≤L nhân số block đã xử lý.

**Lower: adversary đúng phải tạo s private points, không phải s−1.** Trạng thái Q0,Q1 là các điểm đã nhận NO/YES. Với transcript còn consistent và |Q1|<s, trả NO trừ khi NO sẽ hoàn thành một window toàn NO; khi đó trả YES. Mỗi YES mới tại x có witness window I_x mà mọi điểm khác đã ở Q0.

- Adversary còn consistent: một tập≤s hole không thể hit hết m window vì mỗi hole hit L window và m>sL. Trước khi có all-NO window, complement của Q0 có ít nhất s+1 điểm. Vì vậy luôn còn chỗ điền W size s; đây là lemma feasibility, đừng bỏ.
- Không thể dừng an toàn khi |Q1|<s mà chưa có all-NO window. Với mỗi proposed center, nếu window có YES thì unsafe; nếu có unqueried point thì chọn point đó làm hole rồi điền W size s để bác quyết định. Chứng minh fill-set bằng cardinality.
- Witness I_x không chứa YES trước đó vì các điểm khác ở Q0. Nó cũng không chứa YES tương lai vì các điểm khác đã cố định NO. Vậy mỗi trong s witness interval có một private point đối với TẤT CẢ các witness.
- Mọi điểm của các witness đã được query tại lúc YES thứ s. Lower query count≥size union.

**Bổ đề interval đã sửa, có proof sơ cấp.** Với s intervals cùng độ dài L, MỖI interval có private point, union size≥H(s,L). Nếu union là toàn cycle thì m≥sL+1≥H làm xong. Nếu không, cắt cycle tại điểm ngoài union, chuyển sang intervals nguyên trên line; sắp starts x1<⋯<xs, d_i=x_{i+1}−x_i≥1. Có

\[
 |\cup I_i|=L+\sum_{i=1}^{s-1}\min(d_i,L).
\]

Private point của interval giữa i buộc d_{i−1}+d_i≥L+1. Suy ra min(d_{i−1},L)+min(d_i,L)≥L+1. Ghép gap thành từng cặp:

- s=2h+1: h cặp, union≥L+h(L+1).
- s=2h: h−1 cặp và một gap≥1, union≥L+(h−1)(L+1)+1=h(L+1).

Chặn đạt được cho bài toán UNION bằng starts có gaps 1,L,1,L,…; phải nhấn mạnh union construction đạt bound không tự sinh upper decision tree đạt bound.

**Lean sequence MỚI:** `kernel_residual`, `kernel_radius`, `tent_membership`, `consistent_fill`, `terminal_iff`, `forced_yes_has_private_window`, `line_private_union_lower`, `cycle_private_union_lower`, `adversary_depth_lower`, `disjoint_blocks_depth_upper`. Bắt đầu line lemma trên ℤ để tránh ZMod wrap; bridge sang Fin m sau. Không rewrite Finset khi nó nằm trong dependent type `Points W`; U03 đã dùng bridge Prop để tránh lỗi đó.

**Nhánh rủi ro cao: D=H exact.** Muốn đóng upper H phải dựng strategy tree xử lý MỌI reply pattern. Một heuristic “grow then pinch” chưa đủ. Mục tiêu local lemma là recurrence D_s≤L+1+D_{s−2}, D_1≤L, nhưng nếu gặp YES giữa lúc grow thì phải chứng minh invariant còn đủ NO để trả cùng ngân sách. Nếu branch này không đóng, giữ bound factor 2 ở trên; không ép conjecture thành theorem bằng thêm giả thiết về adversary.

**Collision.** “Geometry + query separation” chung đã nằm trong [Javdani et al., Near Optimal Bayesian Active Learning for Decision Making / HEC](https://publications.ri.cmu.edu/storage/publications/pub_files/2014/4/javdani14hec_extended.pdf), gồm overlapping decision regions. [Adaptive Submodular Ranking and Routing](https://arxiv.org/abs/1606.01530) cũng là đối chiếu acquisition/decision-region. Lane đáng thử là luật cụ thể D(m,s,L_ε) được realize trong support radius và query vật lý, đặc biệt dependence vào tolerance và kernel. Tra cứu này chưa chứng nhận luật interval chưa có ở combinatorial search; worker phải tìm thêm theo “search for an empty interval”, “adversarial membership search”, “cyclic windows”, chứ không chỉ tìm tên CIG.

**Nghiệm thu gói 3:** phản ví dụ helper cũ; generic kernel bridge có injectivity; lower với ALL-private; upper sL; counterexample hoặc full strategy tree nếu muốn promote exact parity.

**4. D6/D07 — luật reference có positive part, rồi lớp biên rộng 1/k**

Đây là giá trị minimax STATIC, không gọi nó Γ để khỏi lẫn tốc độ stopping. Đặt k=q+1, t=τ/k, và

\[
 c_k=(1-\tau/k)^{2k-2},\quad
 a_k=(1+(k-2)\tau/k)c_k,\quad b_k=((k-2)\tau/k)c_k,
\]
\[
 e_k=\min(a_k,2b_k),\quad r_k=2a_k-\rho,\quad p_k=\rho-2b_k.
\]

[ReferencePhaseValue](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanD6ReferencePhaseValueV1.lean) định nghĩa

\[
 V_k=\frac{[kr_k-e_k]_+\{p_k(k-1)+[e_k-r_k]_+\}}{4c_k(k-1)}.
\]

[PhysicalCertificate](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanD6ReferencePhysicalCertificateV1.lean) đã nối giá trị này với game thật khi 1≤ρ≤2 và (k−2)b_k≥1, cùng các điều kiện cardinality/reference. Không được bỏ `strong` khi trích theorem.

**Mục tiêu 4a.** Với τ trong compact [τ0,τ1], τ0>0, đặt C=e^(−2τ), A=(1+τ)C, B=τC. Chứng minh

\[
 \frac{V_k}{k}\to G(\tau,\rho)
 =\frac{[2A-\rho]_+(\rho-2B)}{4C},
 \qquad |V_k/k-G|\le C_0/k.
\]

Phải có positive part. [D07_rate_law artifact](/Users/phanan/cig-amf-main/research/high_risk_20260910/D07_rate_law_20260912.json) đã ghi các cell inactive nơi công thức UNCLAMPED âm và sai số scaled diverge. Đừng tốn công prove bản sai đó.

Proof: với 0≤x≤1/2, dùng −x/(1−x)≤log(1−x)≤−x để có |log c_k+2τ|≤(2τ+4τ²)/k. Exp là 1-Lipschitz trên nửa trục âm, suy ra bound cho c_k−C. Suy ra bound a_k,b_k,e_k qua cộng/nhân và Lipschitz của min/max. Trên compact, C có lower bound dương nên denominator ổn. Vì b_k→τe^(−2τ)>0 đều khi τ0>0, điều kiện (k−2)b_k≥1 đúng với k đủ lớn: phải viết lemma eventual này rồi mới áp physical certificate.

**Mục tiêu 4b mạnh hơn, đề xuất mới:** ρ∞=2(1+τ)e^(−2τ), chọn τ sao cho 1<ρ∞<2, và đặt ρ_k=ρ∞+s/k. Khai triển

\[
 c_k=C\{1+(2\tau-\tau^2)/k+O(k^{-2})\},
 \quad a_k=A+C\tau^2(1-\tau)/k+O(k^{-2}).
\]

Đặt E=C min(1+τ,2τ), D=2Cτ²(1−τ)−E. Khi đó

\[
 \rho_k^*=2a_k-e_k/k=\rho_\infty+D/k+O(k^{-2}),
 \qquad V_k(\rho_\infty+s/k)\to\tfrac12[D-s]_+.
\]

Derivation: kr_k−e_k→D−s; p_k→2C; hệ số còn lại trong V_k→1/2. Đây là conjectured theorem có derivation, chưa formalize. Để chứng minh remainder, dùng inequality
0≤−log(1−x)−x−x²/2≤2x³/3 trên [0,1/2], từ derivative x²/(1−x)≤2x² rồi monotonicity/integration. Không rewrite log quotient toàn cục qua x=0.

Lemma MỚI theo thứ tự: `log_one_sub_remainder`, `scaled_reference_expansion`, `strong_eventually`, `physical_value_limit_clamped`, `critical_threshold_expansion`, `critical_window_value_limit`. Ưu tiên finite inequality rồi mới `Tendsto`. Nhánh risky: mở miền `strong` bằng một primal-dual khác; đừng dùng luật ngoài miền để đoán WLOG.

**Novelty:** dependence theo reference/functional ANOVA không mới: [Functional ANOVA with Multiple Distributions](https://arxiv.org/abs/1801.05186), [Lengerich et al., Purifying Interaction Effects](https://proceedings.mlr.press/v108/lengerich20a.html). Candidate riêng là minimax của họ thực, ngưỡng hữu hạn và boundary layer nói trên. Chưa có chứng nhận không collision toàn literature.

**5. Adaptive — dựng scheduler thật trước khi ghép expectation**

Các file solver/tracker mới đọc được ở `/Users/phanan/Documents/ChatGPT/CIG-AMF/work/adaptive_completion_20260912/build/`; đây là nguồn bàn giao, không phải vị trí để worker tiếp tục làm. Nhận các file cần dùng về repo với source hash/receipt tương ứng. `LeanD6ActualDecoderAllocationV1` ở đó còn thiếu compile evidence trong snapshot đã kiểm.

API đã đọc: `full_solver_contract`, `estimated_full_solver_regret`, `adaptive_exploitation_bound`, `decodedWorld_prefix`, `actual_decoder_tail`, `label_iff_geometry`. Đặc biệt `total_query_count` hiện chỉ chứng minh discovery+cyclic+exploitation bằng cùng tổng đổi thứ tự; chưa phải theorem về scheduler.

**Scheduler đề xuất có thể chứng minh:** dùng exploitation counter N. Mỗi khi floor(sqrt N) tăng, lấy thêm một batch discovery và một cyclic round; giữa các lần đó lấy một exploitation query theo tracker. Dùng discovery batch size r0≥512 để tận dụng epoch_tail có sẵn. Khi L_N=floor(sqrt N), discovery sample count là r0(L_N+1), cyclic rounds là max(1,L_N). Raw cost có dạng N+C_q floor(sqrt N)+C'_q với C_q=4|Off j|r0+(2q+1).

State ghi mode, phase index, counts, sums, discovery prefix, cyclic prefix và tracker debt. Mỗi transition đọc đúng một observation mới. Bốn invariant MỚI cần prove bằng induction: query legal; query chỉ phụ thuộc transcript cũ; counts đúng số lần mỗi mode phát query; extracted discovery/cyclic samples có luật thật. Cuối cùng gọi `actual_path_marginals` trên Markov kernel này. Không nhận `hlaw` như assumption của headline.

Chọn Ahat_N bằng decoder hợp lệ có fallback; mhat_N bằng clipped cyclic estimate; ε_N=(N+1)^(−1/4), H_N=ceil(K_q d²/ε_N)+1, d=|allQueries|, K_q=informationCap q. API tracking cho

\[
 \Gamma-I(\bar w_N)\le\frac1N\sum_{u<N}
 \{2L_q|\hat\mu_u-\mu|+\varepsilon_u+K_q1_{\hat A_u\ne A}\}
 +K_qd^2/N.
\]

Dùng Gaussian cyclic law cho E|mhat−μ|≤sqrt(variance)=O_q(N^(−1/4)); discovery tail cho xác suất nhãn sai giảm theo exp(−c sqrt N). Cộng rồi chia N. Thêm dilution factor N/rawCost cho tỷ lệ allocation trên TOÀN bộ query. Các hằng số vẫn phụ thuộc q; đây là fixed-q convergence, chưa phải q-growing theorem.

Nghiệm thu: executable transition hoặc finite measurable transition; theorem counts từ induction; actual law; expectation bound gồm wrong-label term. Không commit vào một Ahat rồi loại bỏ event nó sai.

**6. Adaptive — confidence set, termination và tốc độ kỳ vọng Γ**

Mô hình unit-variance Gaussian, mean query affine m_θ(e)=offset_A(e)+μ slope_A(e), θ=(A,μ), μ∈[0,1]. API hiện có: `actual_mean_affine` trong [GaussianQueryDominance](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanD6GaussianQueryDominanceV1.lean); quadratic nuisance minimization trong các module finite solver.

**Đừng chỉ viết “ghép GLR”. Một construction confidence cụ thể:** N_e(n) là counts và S_e(θ)=Σ_{t≤n,e_t=e}(Y_t−m_θ(e)). Với a>0,

\[
 M_n(\theta)=\prod_e\sqrt{\frac a{a+N_e(n)}}
 \exp\!\left(\frac{S_e(\theta)^2}{2(a+N_e(n))}\right).
\]

Đây là Gaussian mixture của exponential martingale, tích phân λ_e~N(0,1/a) của exp(Σ_e λ_eS_e−λ_e²N_e/2). Proof obligations MỚI: conditional Gaussian mgf với predictable query; nonnegative martingale trước mixture; Tonelli qua mixture; hoàn bình phương tính integral; maximal inequality rồi union hữu hạn→vô hạn.

Đặt

\[
 Q_n(\theta)=\sum_e\frac{S_e(\theta)^2}{2(a+N_e(n))},\quad
 \beta_{n,\delta}=\log(1/\delta)+\tfrac12\sum_e\log(1+N_e(n)/a).
\]

Suy ra P_θ(∀n,Q_n(θ)≤β_nδ)≥1−δ. Confidence set C_n={θ:Q_n(θ)≤β}. Stop khi C_n không rỗng và tất cả θ∈C_n có cùng nhãn A. Với mỗi A, Q_n(A,ν) là quadratic theo ν∈[0,1], nên kiểm điều kiện stop bằng finite min qua A và quadratic clipping; không cần grid trên nuisance.

**Bốn theorem riêng:** (i) statistic measurable/adapted; (ii) τ là stopping time; (iii) δ-correct; (iv) Eτ hữu hạn và rate. Ba theorem đầu không suy ra theorem thứ tư.

Để đóng (iv), cần tự chứng minh, cho mỗi ζ>0 và q cố định, n≥(1+ζ)log(1/δ)/Γ và đủ lớn,

\[
 \Pr(\tau_\delta>n)\le C_{\theta,q} n^p\exp(-c_{\theta,q} n^a),\quad a>0.
\]

Tách bad event của discovery, cyclic estimate, tracking average, và Gaussian observation sums. So Q_n của mọi wrong θ với nI(w_n): hệ số N_e²/(a+N_e) khác N_e không quá a; noise cross term dùng Cauchy–Schwarz, uniform bounded means và finite e. Tổng tail hữu hạn cho Eτ=Σ_nP(τ>n), từ đó limsup Eτ/log(1/δ)≤1/Γ. Đây là mắt khó thực sự, không được đưa tail inequality làm giả thiết rồi báo đã đóng.

Cận dưới matching dùng adaptive KL chain và data processing:

\[
 \sum_e\mathbb E_\theta N_e(\tau)\,\mathrm{KL}(P_{\theta,e},P_{\theta',e})
 \ge\mathrm{kl}(1-\delta,\delta),
 \qquad \mathbb E_\theta\tau\ge\mathrm{kl}(1-\delta,\delta)/\Gamma.
\]

Chuẩn hóa expected counts thành allocation rồi lấy worst alternative. Pinsker chỉ cho một hằng số ở bước này; muốn hệ số log(1/δ) phải giữ binary KL. Nối geometry bằng unique-optimum theorem: source `label_iff_geometry` đã phát biểu equivalence cho retained complement và μ∈[0,1], nhưng phải compile và kiểm phạm vi; với ε-optimal nhiều đáp án, không tự suy ra Γ_label là complexity tối ưu của quyết định.

**q tăng là nhánh khác.** Các remainder cần cùng nhỏ: C_q/sqrt N, K_qd_q²/N, và d_q log n/log(1/δ), cùng constants của estimator/modulus. Full library hiện exponential theo q. Chưa có uniform-q theorem chỉ vì từng q cố định đã xong. Nhánh risky đáng làm là tìm orbit compression hoặc sparse allocation certificate giữ nguyên inf trên mọi alternative; nếu chỉ chọn queries tốt khi đã biết A thì chưa giải quyết discovery.

**Collision:** [Garivier–Kaufmann 2016](https://proceedings.mlr.press/v49/garivier16a.html) đã có Track-and-Stop asymptotically optimal; [Qin–You, Dual-Directed Algorithm Design](https://arxiv.org/abs/2310.19319) có framework thuật toán pure exploration; [Howard et al., Confidence Sequences](https://arxiv.org/abs/1810.08240) có machinery time-uniform. Đây là nền cần cite. Ngược lại [Wang–You 2026](https://arxiv.org/html/2606.21889v1), §6, vẫn liệt kê matching instance-dependent upper bounds và stronger stopping guarantees là việc mở cho ENDS. Không được bảo họ đã đóng điều họ ghi là chưa đóng. Độ mới tiềm năng của mình nằm ở actual D6, boundary regime và q-dependent costs, không ở ký hiệu Γ.

**7. Query — repair đúng bài toán, nhận collision rồi chọn constraint tạo khác biệt**

Cho finite worlds Θ, representation R0, scalar target g, thư viện features h_l với cost c_l. Chọn J, representation mới R_J=(R0,h_J). Theorem MỚI để nối lower đang có với constructive upper:

\[
 \inf_\psi\max_\theta|\psi(R_J(\theta))-g(\theta)|
 =\tfrac12\max_{\text{fiber }F}\{\max_F g-\min_F g\}.
\]

Lower: dùng `E5_response_only_minimax_lower_bound` trong [QuerySufficiencyQuantitative](/Users/phanan/cig-amf-main/work/p13_conjectures/LeanQuerySufficiencyQuantitativeV1.lean) cho hai endpoints. Upper: decoder midpoint mỗi nonempty fiber. Đây là scalar absolute loss, không tự đúng bằng half diameter cho mọi norm.

Repair ở tolerance ε tương đương: với mỗi bad pair có R0 bằng nhau và |gθ−gθ'|>2ε, phải chọn ít nhất một h_l tách cặp đó. Exact ILP:

\[
 \min\sum_l c_lz_l,\quad
 \sum_{l:h_l(\theta)\ne h_l(\theta')}z_l\ge1\quad\forall\text{ bad pair},\quad z_l\in\{0,1\}.
\]

Dual fractional packing cho lower certificate; ILP solution cho upper. Đây chính là một dạng [Test Cover](https://arxiv.org/abs/1212.0117), KHÔNG được quảng bá reduction này là đột phá. Với set-valued safe decisions, phải dùng minimal unsafe subsets/hyperedges, không thay bằng bad pairs vì U03 đã chứng minh pairwise intersections có thể đánh lừa.

Hướng riêng để thử: h_l bị ràng buộc bởi physical intervention, horizon và reuse trên nhiều query; formalize semantics của h_l trong model thật rồi chứng minh cost law theo cấu trúc đó. Nếu chỉ là chọn columns trên finite table thì đóng góp riêng yếu, nên gộp vào Support. Với target estimated bằng interval [lθ,uθ], bad pair được chứng nhận khi khoảng cách hai interval>2ε; upper repair cần diameter của UNION interval trong mỗi fiber≤2ε. Không lọc mất instance target hằng; không dùng keys độc nhất để tuyên deterministic sufficiency.

Nhánh model-based: dùng Bellman recursion để chứng minh g_H target và feature semantics, rồi bound sai số model theo horizon; phải so với [Ferns–Panangaden–Precup, Metrics for Finite Markov Decision Processes](https://arxiv.org/abs/1207.4114). Không gọi representation sufficiency/value error bounds nói chung là mới.

**8. MASTER — cố định world, thay reference; chứng minh giá mua thông tin**

Dùng compensated world F_{A,t0} đã cố định ở reference t0. Đổi reference truy vấn sang t nhưng KHÔNG re-compensate world theo t. Với A/B coordinates, contrast mới của response slopes là

\[
 \gamma(t)=(a(t)-b(t))-(a(t_0)-b(t_0))
 =(1-t)^{2k-2}-(1-t_0)^{2k-2}.
\]

Tại t0 chỉ first-order response bằng nhau. Điều đó KHÔNG có nghĩa mọi raw observation law giống nhau. Worker phải chọn rõ experiment:

- Gaussian response instrument: Y~N(d_i(t),σ²), known variance, query cost κ(t,i)>0. Với hai world khác nhau ở coordinate đang xét, mean gap γ cho KL=γ²/(2σ²).
- Raw samples X,Y=F_A(X)+noise: dù mean response giống nhau, mixture law/variance có thể khác. Nếu X được quan sát và noise Gaussian, full-data KL là E[(F_A(X)−F_B(X))²]/(2σ²), không được thay bằng squared difference của response means.

**Theorem acquisition đích, trước hết hai world:** với Gaussian response model, information-per-cost η(t)=γ(t)²/[2σ²κ(t)], adaptive testing phải trả

\[
 \mathbb E[\mathrm{cost}]\ge\frac{\mathrm{kl}(1-\delta,\delta)}{\sup_t\eta(t)}.
\]

Proof bằng KL chain và mỗi query KL≤supη×cost. Upper fixed-reference, fixed-sample: chọn t* gần tối ưu và threshold ở midpoint; Gaussian tail cho n≥8σ²γ(t*)^(−2)log(1/(2δ)). Đây là matching ORDER, chưa matching leading constant; sequential test và overshoot analysis là phần thêm nếu muốn hệ số sắc.

Với t=t0+h nhỏ,

\[
 \gamma(t)\sim-(2k-2)(1-t_0)^{2k-3}h,
\]

nên sample cost có scale h^(−2), với coefficient phụ thuộc k,t0. Nhánh đáng thử là tradeoff giữa first-order information floor ở t0 và chi phí/reference shift h, dưới cost model có cơ sở thực. h^(−2) tự nó chỉ là Gaussian testing cũ. Nếu chỉ có CLT sample-count approximation trong script thì chưa có finite-confidence evidence.

**Collision cần sửa cho đúng:** [Bennouna et al., Data Informativeness in Linear Optimization under Uncertainty](https://arxiv.org/pdf/2602.15365) có combinatorial application và noisy-observation guarantee (Proposition 10), không chỉ LP noiseless. [Cost Aware Best Arm Identification](https://arxiv.org/abs/2402.16710) khiến tỷ số KL/cost nói chung không mới. Lane riêng phải là fixed physical world, những kênh evidence khác nhau, và matching cost để phá floor của cùng một terminal decision. Contract `sound` cần được chứng minh từ construction này, không nhận nó làm field giả thiết.

**Thứ tự giao ngay và tiêu chí dừng**

| Worker | Sản phẩm đầu tiên | Phần mở sau đó | Dừng/hạ claim khi |
|---|---|---|---|
| Functional | Hai family η với bounds 9η và (1+3η)/(16η) | Oracle exact, allocator vs C_lucb | Coupling làm hỏng block separation; allocator không hơn baseline thì không claim advantage |
| Structural | Approximate-anchor induction và menu bound | Computable next, oracle-call tradeoff | Chỉ đổi wrapper thì không gọi theorem novelty mới |
| Support | Refute helper cũ; all-private line lemma | Physical tent, lower H, upper sL; thử exact H | Pinch strategy có branch vượt H thì giữ factor-2 theorem |
| D6 static | Positive-part limit và eventual strong | Boundary layer V→[D−s]+/2 | Ngoài miền physical certificate thì chưa gọi actual minimax |
| Adaptive scheduler | Một transition và bốn invariants | Actual path + expected allocation regret | Chỉ identity cộng counts thì chưa scheduler closure |
| Adaptive stopping | Gaussian mixture confidence set | Tail of τ, Eτ, matching KL lower | Chỉ δ-correct/a.s. finite thì chưa expected Γ |
| Query | Fiber midpoint upper + repair certificate | Physical intervention/horizon constraint | Generic Test Cover thì gộp, không dựng paper riêng từ tên mới |
| MASTER | Fixed-world response contrast, xác định observation law | Information-cost lower/upper và evidence floor | Same mean không same law; cost tùy đặt thì phase thiếu ý nghĩa |

Các nguồn trên xác nhận collision gần và phạm vi khác nhau. Tra cứu không chứng minh được “chưa ai làm”. Muốn claim priority, worker cần một bảng theorem-to-theorem: assumptions, observation model, answer set, complexity, theorem của prior, theorem của mình. Nơi chưa có theorem vượt prior thì ghi là hướng thử, không ghi novel/proved.
