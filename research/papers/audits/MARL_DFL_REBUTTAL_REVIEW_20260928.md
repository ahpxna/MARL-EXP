# Audit phản biện về DFL — 28/09/2026

Đọc trainer v3/v6, protocol DFL đang có, profile feature/mask, JSON jobs và nhãn train của scratch s3/BC s3. Tính thống kê từ nhãn có sẵn, không rollout/train. Đối chiếu nguồn gốc về optimizer's curse, BCQ, CQL, clustered inference và paired permutation. Amendment được đề xuất trong lời worker; file PROTOCOL_E3_DFL lúc kiểm vẫn chứa grid T cũ, không giả định Amendment đã freeze.

## Verdict

Phản biện phần lớn hợp lý. Giữ MSE-feasible, công nhận R1 như regularizer là giả thuyết, dùng controls cố định và tuning grid đối xứng. Không nhận câu sign-flip exact cho null mean không điều kiện, không coi coefficient/label-variance diagnostic là causal proof, không bỏ qua smoke đã in DEV.

## (a) Feasible mask

Tính lại 768 train state/actor, prefix luôn hợp lệ, mask bytes <= b0 + 74:

| actor | feasible | sd feasible / infeasible | fraction sum gain² from infeasible |
|---|---:|---:|---:|
| scratch s3 | 98.0785% | 7.2164 / 10.9736 | 4.3327% |
| BC s3 | 97.8937% | 7.0097 / 11.4348 | 5.5551% |

Tỷ lệ worker báo khớp; BC squared-label share gần 5.6%, không 4–5%. Quan trọng hơn, sum gain² là loss của predictor zero (và thống kê pooled), KHÔNG phải share MSE residual của critic đã học. Objective code là per-state mean residual². Muốn đo share lỗi thật phải dùng prediction/checkpoint, với đúng weighting. Không cần làm thêm để quyết định giữ control nhỏ; tuyệt đối không suy 'chỉ chiếm x% nên tác động lên argmax phải nhỏ'.

## (b) R1 regularization

Đồng ý. Oracle superset inequality không xếp thứ tự chất lượng thực của learned argmax. Restriction có thể giảm cơ hội chọn candidate được đánh giá quá cao. Smith–Winkler là nguồn trực tiếp; BCQ là analogue về hạn chế action theo support. CQL regularizes Q-values, không phải hard radius quanh prefix. Những nguồn này không chứng minh R1 hiện tại là support constraint hay rằng cơ chế gây ra số đo hiện tại.

Recheck saved legal jobs: scratch direct mean -0.1875, R1 -0.4444; BC direct -1.3125, R1 -0.3681. Số worker làm tròn khớp. Cải thiện R1 ở vài arms phù hợp regularization hypothesis, chưa identify optimizer's curse: khác oracle quality, candidate pool, threshold và error structure cũng ảnh hưởng; cần paired uncertainty để claim difference.

Chấm một evaluator train trên direct rồi restrict R1 là ablation hợp lệ: giữ evaluator cố định, đo ảnh hưởng restriction. Không phải code sai hay model invalid. Nhưng để hỏi best learned R1-DFL đạt được gì, phải train loss trên C_R1 và tune checkpoint/tau riêng cho R1. Hai estimand khác nhau. Hoãn training R1 riêng đến sau direct pilot là hợp lý.

## (c) Eight clusters and sign flip

Worker đúng: 304 dense state vẫn chỉ 8 traffic-seed clusters. Percentile bootstrap không được đọc như bảo đảm độ phủ finite sample với 8 clusters. Cameron et al. chỉ ra inference vấn đề khi ít clusters; kết quả regression/wild bootstrap không tự chứng minh mọi percentile interval ở đây đều undercovers hoặc mọi sign flip đều sửa được.

Duyệt 2^8 = 256 sign vectors chỉ loại Monte Carlo error. Để p-value exact cần null sign-invariance (ví dụ các seed differences độc lập và đối xứng quanh 0), hoặc một randomization design cho phép hoán nhãn. E[D]=0 không đủ. Hai policies cùng chạy trên cùng scenario không tự tạo random treatment assignment.

Phản ví dụ tự suy ra: D=+1 với xác suất .9, D=-9 với xác suất .1, E[D]=0. Với 8 seed độc lập, xác suất thấy cả 8 dương là .9^8=43.05%. Khi đó sign-flip mean test một phía có p=1/256 và reject .05. Type-I error ít nhất 43%, dù duyệt đủ mọi sign vector. Đó là lỗi giả thiết, không phải thiếu permutation.

Khuyến nghị: sign flip được dùng như DEV screening statistic với giả thiết đối xứng khai báo rõ, không như theorem mean superiority distribution-free. Báo vector 8 paired seed means, effect size, CI hiện có và leave-one-seed-out sensitivity. Không chọn test theo cái nào significant. Nếu không bảo vệ được symmetry, giữ p-value là sensitivity; đừng gắn nhãn exact significance. Một sign test trên dấu có thể không cần symmetry, nhưng test probability/median chứ không cùng estimand mean waiting.

Closed loop trên 16 seed x 2 load x 5 actor mạnh hơn về evidence, nhưng không có 160 replications độc lập: actor và traffic seeds là các nguồn dependency; vẫn cần paired/crossed-cluster treatment. Nếu panel đó đã dùng phát triển trước đây, nó vẫn là development, không thành confirmation vì thêm actor.

## (d) Baselines and intersection-union

Đồng ý không chọn winner trong 20 DEV arms rồi coi là baseline đã định trước. MSE-all và MSE-feasible là fixed matched controls hợp lý, với tune trên SELECT.

IUT đúng nếu mỗi component test valid level alpha và một method/comparison family được cố định: H0 là ít nhất một mean contrast <=0, H1 là mọi contrast >0; reject khi tất cả component reject. Không cần independence giữa component tests hay Bonferroni cho global conjunction. Điều này không chữa invalid component p-values, chọn method trên DEV, nhiều cap/endpoint rồi chọn kết quả đẹp, hay repeated protocol revisions.

Nếu claim cả 'thắng prefix và cả hai MSE', đưa prefix vào conjunction. Chỉ sample mean >0 so prefix cộng significant vs hai MSE chưa chứng minh positive mean gain, vì cả hai MSE có thể âm. DEV có thể dùng rule đó như screening nhưng không gọi là full statistically demonstrated benefit.

## Cap dependence

Rủi ro transfer là thật: DFL train ở total allowance +84 B với 10 B bid, tức payload/profile slack +74. Không gọi +74 là total cap, và +84 là allowance trên b0 chứ không phải absolute total bytes.

Không bắt buộc train model riêng cho mỗi cap hoặc có cap input: shared scorer có thể rank cùng candidate values rồi mask theo cap. Nếu muốn generalization/robustness, phải chứng minh bằng evaluation. Multi-cap DFL có thể sample cap và áp mask tương ứng, có hoặc không thêm cap input; hyperparameter/threshold phải chọn theo policy ngân sách khai báo. Value-MSE current labels/candidate distribution cũng không tự cap-independent về performance.

Đề nghị vòng này giữ primary cap +84. Các cap khác là secondary transfer, chưa mở thêm full budget-conditioned training chỉ vì có endpoint option (c).

## Chốt bốn lựa chọn

1. Chọn T=1 cố định, cùng lr grid {3e-4,1e-3,3e-3}, cùng init/update budget, chọn trên SELECT. Đây là cách cân bằng hợp lý, không là chứng minh mỗi objective đã được tune tối ưu. Lưu chi phí label/training/tuning/inference riêng.
2. Sign flip: chỉ screening dưới giả thiết công khai và kèm sensitivity, không thay percentile bằng một 'exact guarantee'. Giữ dữ liệu seed-level để reviewer kiểm được. Final inference và practical effect threshold chốt trước final panel.
3. Chưa thêm DFL-no-bid vào vòng primary kiểm loss. Sau nếu DFL có tín hiệu, thêm no-bid/same-byte bid controls trước claim contribution của bid. Không giả vờ loss comparison đã chứng minh bid giúp.
4. Hoãn R1-DFL riêng. Giữ current shared-evaluator R1 như descriptive ablation.

Với 3 trained arms x 3 learning rates x 3 initialization seeds là 27 critic fits/actor, prefix không cần train; head có thể freeze/reuse theo init với provenance. 45 chỉ đúng khi có thêm 2 trained arms hoặc work khác, cần job matrix giải thích. Ưu tiên scratch s3; BC descriptive không phải điều kiện để quyết định phát triển method.

Smoke 4 epoch đã in DEV -0.75: Amendment phải ghi 'sau smoke, trước full amended runs'; không ghi trước mọi run hoặc chưa từng thấy DEV. Disclosure đúng nhưng không xóa việc đã xem DEV. Toàn vòng này vẫn exploratory development; final 1301–1316 giữ kín.

## Nguồn

- Smith & Winkler (2006), optimizer's curse: https://pubsonline.informs.org/doi/abs/10.1287/mnsc.1050.0451
- Fujimoto et al. (2019), BCQ: https://proceedings.mlr.press/v97/fujimoto19a.html
- Kumar et al. (2020), CQL: https://proceedings.neurips.cc/paper/2020/file/0d2b2061826a5df3221116a5085a6052-Paper.pdf
- Cameron & Miller (2015), review including Cameron–Gelbach–Miller (2008), few clusters: https://cameron.econ.ucdavis.edu/research/Cameron_Miller_JHR_2015.pdf
- SciPy permutation_test official documentation, paired-samples null/assignment assumptions: https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.permutation_test.html

Không có priority/novelty claim mới. Không tự sửa frozen protocol, dừng job hoặc khởi chạy 27/45 fits trong audit này.
