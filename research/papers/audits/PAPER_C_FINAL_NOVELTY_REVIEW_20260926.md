# Paper C — kiểm novelty cuối cho phạm vi hiện tại

Ngày 26/09/2026. Kết hợp audit nội bộ trước đó (Lean/model/script/JSON) với lượt đối chiếu literature này. Không chạy lại Lean, LP hay simulation. Không tuyên bố đọc toàn bộ corpus 500/1000 bài; lượt này đọc các định nghĩa, theorem và phần lập luận liên quan trong những nguồn gần nhất dưới đây, cùng manuscript C hiện tại.

## Quyết định

**Có thể chốt phạm vi nghiên cứu hiện tại của C để gửi giáo sư/reviewer.** Có một bộ đóng góp toán riêng, đủ rõ để bảo vệ novelty ở mức bài lý thuyết chuyên sâu. Chưa tìm thấy kết quả tương đương trong các nguồn đã kiểm. Đây không phải bằng chứng tuyệt đối không tồn tại prior art, không phải cam kết acceptance, và không phải đánh giá “10/10 breakthrough”.

Không cần biến odd/repeated-type one-exchange, online budget streams hoặc closed form cho mọi multiset thành điều kiện mới để hoàn tất bài hiện tại. Chúng được giữ ngoài headline đã chứng minh.

## 1. C thực sự trả lời câu hỏi nào?

Một law trên permutation phải tốt cho mọi budget, dưới band trên marginal của từng item. Objective:

V_g(eta) = inf_{P feasible} max_{0<k<m} E_P[(|sum_{j<=k} g_{pi_j}| - b_k(g))/||g||_1],

với b_k là optimum riêng ở cardinality k và |Pr(i trong prefix_k)-k/m|<=eta/m.

C trả lời giá của việc phải cam kết vào một law chung, cách giá đó phụ thuộc cấu trúc signed weights, khi nào biết budget làm thay đổi optimum, và trong những họ nào một exchange đủ để đạt benchmark budget-aware.

Đây là câu chuyện thống nhất. Không nên trình bày thành bộ sưu tập các LP hoặc chỉ nhấn mạnh số theorem Lean.

## 2. Đối chiếu gần nhất, ở cấp statement

### Storandt–Funke 2019: đã có regret-minimizing permutations

Phần permutation ở trang 1603 tối ưu tổng average regret qua prefixes; Theorem 16 cho greedy approximation của accumulated happiness. Vì vậy “một ordering tốt cho mọi budget” không mới.

C khác ở minimax expected signed-cancellation regret, law ngẫu nhiên dưới item bands, công thức exact và attaining law cùng phục vụ mọi k. Theorem 16 không suy ra các frontier của C.

Nguồn: https://ojs.aaai.org/index.php/AAAI/article/view/3975/3853

### Singh–Kempe–Joachims 2021: đã có marginal constraints cho mọi item/k

Definition 2.1 ràng buộc cumulative rank probabilities; Eq. (3) tối ưu utility tuyến tính trên rank marginals. Không nhận all-prefix marginals hoặc random rankings là mới.

C's absolute prefix loss cần joint law. Ví dụ cùng uniform rank matrix với (+,+,-,-): cyclic alternating order cho E|prefix_2|=0, cyclic block order cho 1. Do đó không thể dùng nguyên marginal utility LP để suy các values của C. Đây là lý do cần count-state occupancy, không phải phát minh ra LP.

Nguồn: https://www.cs.cornell.edu/~tj/publications/singh_etal_21a.pdf

### Celis–Straszak–Vishnoi 2018; Ando–Yokoi 2026

Prefix representation constraints và flag-matroid constrained ranking đã có. Ando–Yokoi tối ưu Kendall distance đến ranking cho trước, với prefix feasibility, không phải expected signed-prefix regret dưới probability bands. Không đồng nhất ex-post quota với ex-ante marginal band.

Nguồn: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.28
https://arxiv.org/html/2607.07153

### Incremental maximization

Bienkowski et al. Theorem 1 cho competitive ratio khoảng 1.373 với monotone submodular objective, Theorem 2 lower bound 1.25. Đây là prior trực tiếp cho consistent prefixes; không là nghiệm của signed regret không đơn điệu dưới marginal bands.

Nguồn: https://arxiv.org/html/2606.28558

### Koike–Lin–Wang: joint mixability

Section 4, Eqs. (8)–(13), đã tối ưu worst-case expected cost của subset sums dưới prescribed marginals. Theorems 4–5 cho kết quả quadratic cost với symmetric subset uncertainty. Đây gần C hơn chỉ nói “coupling literature”. Không nên nói lĩnh vực này không có permutations.

C thêm realization là một multiset cố định, nested prefixes, item bands, absolute loss trừ b_k và các exact family values. Các kết quả đã đọc không cho những công thức đó.

Nguồn: https://arxiv.org/html/2204.11438

### Bellini–Karasan–Pinar 2016

Column permutations, mixability gaps và maximum-flow methods đã có; Theorem 3 còn có điều kiện parity cho complete consecutive integer matrices. Do đó “có parity”, “dùng permutation” hoặc “dùng flow” không tự là novelty.

C cần giữ claim cụ thể về all-prefix marginal-regret frontiers và breakpoint, không generic parity phenomenon. Bellini tối ưu extreme row sums của matrix qua column permutations, khác feasible laws và objective của C.

Nguồn: https://repository.bilkent.edu.tr/bitstreams/4e7bc6f3-b404-426a-b768-29db24e9fecd/download

### Prefix discrepancy / Steinitz

Bansal et al. định nghĩa prefix discrepancy bằng chọn signs cho fixed vector sequence; Steinitz liên quan rearrangement của vector sums. Đây là prior cho prefix balancing. C giữ dấu cố định, tối ưu distribution trên orders, có budget-specific baseline và marginal restrictions. Generic balancing không suy ra exact price curve.

Nguồn: https://arxiv.org/pdf/2111.07049

### Recoverable selection: prior còn thiếu quan trọng nhất

Chassein et al. cho chọn p items trước, rồi đổi tối đa k items sau khi cost scenario lộ ra. Limited exchange after reveal đã có; không nhận nó là framework mới.

C giữ weights biết trước, reveal cardinality, initial law phục vụ tất cả cardinalities, có band cho initial/final laws. Kết quả riêng là ngưỡng chính xác của lợi ích biết budget và V^(1)=B trên phạm vi nêu trong theorem.

Nguồn: https://arxiv.org/pdf/1701.06064

Hommelsheim et al. 2026 nghiên cứu commitment sau failures: giữ các item sống sót và thêm có giới hạn. Đây cũng là neighbor mới, nhưng commitment có nghĩa khác C's commitment to one ranking law.

Nguồn: https://link.springer.com/article/10.1007/s10107-026-02385-7

Nasrabadi–Orlin đã có robust incremental recourse từ 2013; Gupta et al. xét dynamic discrepancy với recourse là sign changes. Các cơ chế recovery này là nền, không thay cho exact value của C.

Nguồn: https://arxiv.org/html/1312.4075
https://arxiv.org/abs/2111.06308

### Randomized minimax regret

Mastin–Jaillet–Chin dùng zero-sum game và LP cho randomized minimax regret (Eq. 11, Theorem 1). Không nhận minimax randomization hoặc LP duality là mới. C's solved values and constrained prefix-law geometry remain the distinguishing results.

Nguồn: https://www.mit.edu/~jaillet/general/rand_mmr_final.pdf

## 3. Bộ contribution đáng giữ

1. Exact parity frontiers cho mọi m trong phạm vi và mọi eta, với cùng một attaining law qua mọi budget. Even frontier max{2/((m+4)(m-1)),4(1-eta)/(m(m+4))}; odd có hai active affine pieces trước free value. Zero-band price <2 phía chẵn và Theta(m) phía lẻ.
2. Các frontiers theo magnitude ratio cho bốn count patterns, có matching certificates và attaining constructions. Đây mở rộng khỏi một normalization đặc biệt; vẫn không phải theorem closed form cho mọi counts.
3. Exact value của budget information: A=V-B có onset chính xác; V^(1)=B trên four-item và even g_m family. Câu hỏi có ý nghĩa: khi nào thật sự đáng adapt sau reveal, và cần sửa bao nhiêu? Không claim online adaptation.
4. Robust-ball floor Theta(min{m,1/epsilon}) với baseline và denominator tính lại, quantifier là infimum trên ball. Không đọc thành mọi perturbation đều collapse.
5. Exact typed-flow/count-transport representation bảo toàn objective, bands và item-level edits. Machinery cổ điển, nhưng là cầu nối cần thiết để finite computation và family theorem nói cùng một problem.

Contribution 1–4 là nội dung toán; Lean tăng độ tin cậy, không thay bằng chứng novelty.

## 4. Những phản biện còn có thể xảy ra

- Vì sao signed-prefix model đáng nghiên cứu? Phải giữ physical bridge shared binary support và giải thích cancellation/commitment. Không quảng cáo như kết quả cho mọi neural compression hay traffic controller.
- Công thức chỉ là giải LP nhỏ? g_m là infinite all-m family; heterogeneity có symbolic continuum; lower certificates và constructions là lý do các kết quả hơn finite enumeration. Không lấy số region lớn làm giá trị tự thân.
- Generality còn hẹp? Đúng với closed forms. General typed LP và robustness mở rộng đối tượng, nhưng chưa làm closed form mọi multiset. Đây là limitation hợp lệ, không phải gap che giấu.
- Figure không chứng minh theorem: giữ exact lines, numerical markers và attained search points tách biệt. Existing C data đã audit ở báo cáo trước; không có lý do chạy thêm seeds để trả lời novelty.

## 5. Các sửa trực tiếp trong lượt này

Đã chỉnh riêng phần related work, comparison table và bibliography của paper_c.tex: thêm Storandt–Funke, Bellini et al., Bansal et al., Ando–Yokoi, Chassein et al., Hommelsheim et al. Sửa câu phủ định quá rộng về permutation trong mixability. Không đổi mathematical claims/Lean/ledgers. Native LaTeX editor compile SUCCESS.

## 6. Điều kiện đóng C và chuyển A/B

- Giữ theorem scope hiện tại; odd/repeated-type one-exchange ngoài phạm vi được ghi NUMERICAL/open nếu chưa có endpoint đã kiểm.
- Đồng bộ final supplement/claim map với main; không để ghi chú tiến độ cũ thành phát biểu khoa học.
- Chốt một snapshot gate/source/figure/citation cho bản gửi; audit trước xác nhận các cited chains có current complete PASS closures. Không cần chạy lại experimental LP cho novelty.
- Giáo sư cần đọc bản cuối và chọn venue phù hợp. Không cần mở thêm hướng toán chỉ để trì hoãn việc gửi.

**Đề xuất cuối: chốt research scope C. Novelty ở exact quantitative laws của problem này có cơ sở để defend; còn việc release/editorial cuối, không còn yêu cầu nghiên cứu mới bắt buộc được phát hiện qua lượt literature này.**
