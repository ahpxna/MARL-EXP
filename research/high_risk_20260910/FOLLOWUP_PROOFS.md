# Structural, Support và bước khám phá A của D6

Đây là ghi chú chứng minh đang làm, không phải addendum cho paper. Trạng thái compile lấy từ manifest đi kèm; các kết luận về thuật toán D6 đầy đủ không được nâng hạng từ simulation.

## Structural: tolerance cố định

Đặt R(S)=selectedRadius(F,S), c_i=osc(F_i)/2. Với S⊆T:

|R(S)−R(T)| ≤ ∑_{i∈T\S} c_i.

Proof: tổng residual trên Sᶜ là tổng residual trên Tᶜ cộng tổng các component thuộc T\S; dùng bất đẳng thức dao động và subadditivity. Không cần R monotone hay submodular.

Nếu c_i≤c và S là optimum ở budget k, mọi extension P⊇S ở budget l≥k thỏa

R(P)−min_{|T|=l}R(T) ≤ 2c(l−k).

Thật vậy, lấy R₀⊆T với |R₀|=k. Hai lần thay đổi tập tốn c(l−k), còn R(S)≤R(R₀).

Lấy một ranking đi qua optimum tại mỗi budget 0,h,2h,...,⌊m/h⌋h. Với budget k, dùng ranking của anchor ⌊k/h⌋h. Suy ra

χ_{2ch}(F) ≤ ⌊m/h⌋+1, h≥1.

Hệ quả đã compile trong `LeanStructuralBalancedFixedToleranceV1`: nếu m≥K≥1 và c_i≤C/m, thì χ_{2C/K}(F)≤2K. Lấy h=⌊m/K⌋; dùng hK≤m<(h+1)K≤2hK. Với m<K, cận exact m+1 cũng hữu hạn theo K.

File Lean: `LeanStructuralToleranceBudgetNetV1`. Đây là upper bound cho actual support geometry, không phải giả thiết Lipschitz được nhập vào. Lớp balanced có c_i≤C/m cho cận số ranking độc lập m ở tolerance cố định. Toàn lớp chỉ có ∑c_i=1 vẫn mở: không được suy c_max=O(1/m) từ chuẩn hóa tổng.

Tìm kiếm mới: 120 instance (scalar hoặc bốn tip + anchor), m=8,10,12; mỗi instance kiểm tra exact tại epsilon=1/20,1/10,1/5. Không thấy χ>2. Thuật toán giữ antichain coverage masks tại từng subset, rồi giải set cover trên tập budget. Dominance pruning an toàn vì các đường tới cùng subset có cùng mọi continuation. Kiểm tra đối chiếu instance scalar chi5 cũ cho đúng curve 5→3→2→1 tại bốn mốc đã biết. Không suy universal bound từ random search này.

## Support: cùng primitive, khác geometry và độ khó query

Giữ tip t_w có coordinate w bằng 2−m và mọi coordinate khác bằng 1. Bây giờ world W có support

S_W={0}∪{t_w:w∈W}.

Primitive vẫn là coordinate projections. Với quyết định giữ j:

R_W({j})=(m−1)/2 · 1{j∈W}.

Bởi tổng coordinate mỗi tip bằng 1, residual bỏ j tại t_w bằng (m−1)·1{j=w}. Anchor cho residual 0. Membership vật lý của t_a tương đương a∈W; không phải oracle trả hidden label.

Hai họ đối chứng:

* |W|=1: minimal bad fibre có m world, nhưng một membership query đủ chọn quyết định safe (đã prove trước).
* W=[m]\{w}: mỗi world chỉ có quyết định safe w. Hai world khác nhau đã bất tương thích. Mọi deterministic adaptive membership tree đúng trên mọi world có depth≥m−1; cây hỏi lần lượt m−1 tip đạt equality.

Proof lower: theo nhánh toàn positive của cây, gọi Q tập tip đã hỏi và j output. Nếu w∉Q, transcript của world thiếu w chính là nhánh đó, nên soundness ép j=w. Do đó tất cả world index nằm trong Q∪{j}; m≤|Q|+1≤depth+1. Proof upper: hỏi m−1 tip; negative đầu tiên là hole, hoặc suy ra tip cuối bị thiếu.

File Lean: `LeanSupportMultiTipGeometryV1`, `LeanSupportAdaptiveQuerySeparationV1`. Scope cận cây: deterministic, worst-case, zero-error, unit-cost individual tip membership. Không tự mở rộng sang noisy, randomized expected cost hoặc group membership.

Exact DP trên toàn bộ world |W|=s kiểm tra 36 case, 2≤m≤9, 1≤s<m, cho optimum worst-case queries=s. Luật toàn bộ s chưa được formalize. Proof dự kiến: ≤s bằng hỏi s tip rồi suy ra nếu tất cả positive; ≥s bằng nhánh positive dài <s, hoàn thành một support s-tip chứa cả queried tips và output. Thêm cardinality prior là thông tin thuật toán thực sự dùng.

Các kết quả này loại bỏ cách dùng bậc obstruction đơn độc làm acquisition complexity. Chưa đủ khẳng định novelty của một framework: decision-region determination và hyperedge cutting đã mô hình hóa decision regions lẫn test incidence [Javdani et al. 2014](https://arxiv.org/abs/1402.5886). Phần cần nghiên cứu tiếp là luật chi phí đặc thù của support geometry dưới query bị giới hạn, có cận khớp và nhiễu.

## D6: khám phá nhãn không phụ thuộc nuisance mu

Giả sử j và q được biết, U=[2q+2]\{j}, |U|=2q+1, B=U\A, |B|=q. Đặt b_i=1{i∈B}. Chọn anchor a và với mỗi i≠a một helper k khác a,i,j. Chỉ cần q≥2 để các pair off queries hợp lệ. Mean thật:

u_i=1−mu b_i;
p_{i,k}=1+(1−mu)(b_i+b_k).

Vì thế

u_a−u_i+p_{i,k}−p_{a,k}=b_i−b_a.

Construction chọn index trước khi biết A hoặc mu. Bốn fresh query có unit Gaussian noise độc lập tạo contrast N(b_i−b_a,4). `LeanD6NuisanceFreeDiscoveryV1` prove actual means, legality và decoding gap; `LeanD6NuisanceFreeDiscoveryLawV1` nối vào canonical product Gaussian law.

### Thuật toán và proof termination của riêng bước discovery

Đây là proof toán học; chưa phải theorem Lean về stopping time. Nó không chứng minh termination hoặc Gamma-rate của full adaptive D6 algorithm.

Đặt d=2q. Tại stage s dùng r_s=2^s repeat cho mỗi contrast, tính sample means z_i; score anchor bằng 0. Tổng chi phí tới stage s là 4d r_s. Mỗi score khác anchor có mean b_i−b_a, variance 4/r_s. Chọn q score cao nhất làm Bhat. Với 0<delta<1, đặt

c_s = sqrt[(8/r_s) log(2d(s+1)(s+2)/delta)].

Dừng nếu khoảng cách giữa score thứ q và thứ q+1 (sắp giảm dần) lớn hơn 2c_s.

Gaussian tail + union bound cho

P(max_i |z_i−(b_i−b_a)|>c_s) ≤ delta/[(s+1)(s+2)].

Tổng qua s là delta. Trên complement của union đó, mỗi output có Bhat=B: nếu chọn nhầm thì có một cặp true-B/true-A đảo thứ tự với empirical gap>2c_s, mâu thuẫn mean gap 1 và hai sai số ≤c_s. Do đó thuật toán delta-correct.

Để chứng minh termination, không được chỉ xét good event xác suất 1−delta. Chọn s0 sao cho c_s≤1/8 với mọi s≥s0, tồn tại vì log(s)/2^s→0. Nếu tất cả score error≤1/4 thì empirical true-B/true-A gap≥1/2>2c_s, nên đã dừng. Do đó với mọi s≥s0:

P(T>s) ≤ 2d exp(−2^s/128).

Cận này tiến về 0, nên P(T=∞)=0, kể cả ngoài event simultaneous coverage. Tail-sum cho chi phí N=4d2^T:

E N = 4d[1+∑_{s≥0}2^s P(T>s)]
    ≤ 4d[2^{s0}+2d∑_{s≥s0}2^s exp(−2^s/128)] < ∞.

Nếu r0=2^{s0}≥256 thì dyadic integral bound cho tổng cuối ≤256 exp(−r0/256), nên

E N ≤4d[r0+512d exp(−r0/256)].

Đây là upper bound O(q(log(q/delta)+log log(q/delta))) cho một thuật toán discovery cụ thể, không phải lower bound hay chi phí tối ưu. Các hằng số khá bảo thủ.

Simulation: 144 cell, q=3,4,8,16,32,64; mu=0,.01,.5,.9,.99,1; bốn hidden-label patterns/cell; 200 trial/pattern, tổng 28.800 trial. Không censor, không thấy false label. Mean queries khoảng 15.053–579.338. Dùng Gaussian sufficient statistics chính xác cho batch raw queries và tính đủ bốn observation/repeat; không diễn giải thành 28.800 lần chứng minh termination.

### Còn thiếu để đạt regret và Gamma

1. Formalize Gaussian tail, first-passage time và expectation của discovery trên một probability space chung; law của một block chưa thay thế bước này.
2. Ghép discovery với phase estimation và allocation. Nếu commit vào Ahat sau một lỗi xác suất delta0, expected regret phải chứa loss_on_wrong_A × delta0. Không được bỏ term đó.
3. Muốn E tau/log(1/delta)→1/Gamma cho q cố định: discovery có confidence log(1/delta) cùng bậc có thể làm hỏng hằng số. Cần exploration/tracking có chi phí o(log(1/delta)), revalidation và chứng minh uniform integrability/tail, thay vì một recover-first commit cố định.
4. Khi q tăng cùng ngân sách: upper bound discovery hiện là O(q log(q/delta0)). Nếu phase budget chỉ N=Theta(q), nó không thể được xem là negligible theo upper bound này. Điều đó chưa chứng minh mọi thuật toán phải trả chi phí đó. Cần lower bound hoặc khai thác large legal queries.

Khám phá support từ pooled noisy counts liên quan trực tiếp quantitative group testing. [Li et al. 2026](https://arxiv.org/html/2601.11797v1) nghiên cứu random nonadaptive design trong chế độ số defective sublinear và Gaussian noise với cận trên/dưới. D6 có dense |B|=q trong 2q+1 coordinate, unknown multiplier 1−mu, row legality và mục tiêu adaptive allocation/stopping. Phải đối chiếu các giả thiết đó trước khi dùng định lý của họ; contrast triệt nuisance tự nó chưa đủ claim một sample-complexity breakthrough.


### Đường đối chiếu để đóng Gamma ở q cố định

[Degenne–Koolen–Ménard, NeurIPS 2019, Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/8d1de7457fa769ece8d93a13a59c8552-Paper.pdf) cho cận kỳ vọng từ game value, regret của hai learner và remainder dưới tuyến tính, trên model mean bị chặn. Đây là nguồn cần dùng để kiểm phép giảm; chưa phải theorem về runner D6 hiện tại.

Ánh xạ dự kiến: arm = từng legal query; model = vector actualMean(A,mu); answer = A; alternative = nhãn khác; Gaussian KL = information. Với q cố định, số arm và nhãn hữu hạn, model là hợp hữu hạn các đoạn affine. Cần đóng injectivity theo nhãn, boundedness, positivity và best-response oracle, rồi đối chiếu chính xác tracking/stopping. Nếu dùng route này, asymptotic Gamma-rate là specialization của framework đã có. Phần novelty phải nằm ở luật theo q, biên pha và chi phí khám phá; không được gán novelty cho định lý generic.
