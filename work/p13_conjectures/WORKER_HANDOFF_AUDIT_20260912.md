# Audit và giao việc sau D03 / S02 / U03 — 2026-09-12

Đây là bản bàn giao mới thay cho câu “S02/U03 chưa được tạo”. Không sửa artifact lịch sử. Audit này không chạy lại Lean hoặc thí nghiệm. Không gửi việc cho subagent/task nào; các gói dưới để người dùng giao worker.

## 1. Trạng thái đã kiểm trên đĩa

| Mục | File trong work/p13_conjectures | Audit sạch | Phạm vi |
|---|---|---:|---|
| D03 | LeanD6ReferenceResponseJoinV1 | 29 | Mức response thật và compensation của slope; chưa là same-Q centered family hay minimax thật |
| S02 | LeanStructuralToleranceQuantifiersV1 | 7 | Universal numerical upper; staircase fixed-epsilon bounded/eventually one; diagonal lower |
| U03 | LeanSupportObstructionQueryOrderV1 | 17 | Mọi obstruction tối tiểu; sparse depth 1, dense depth m−1, cùng physical membership |
| D05, phần đại số | LeanD6ReferencePhaseValueV1 | 19 | Domination theo d, endpoint theo h, equalizers và probability weights của reduced game |
| D06, phần đại số | LeanD6ReferencePhaseThresholdV1 | 6 | Positivity threshold của biểu thức phaseValueFull |

Cả 78 audit print chỉ dùng propext, Classical.choice, Quot.sound; không lỗi trong log; source không mới hơn log/olean; không token sorry/admit/native_decide trong năm source này. Đây không phải census toàn corpus hoặc clean rebuild. D03 có receipt exit 0 và hash source khớp. S02/U03 không có receipt exit-code độc lập trong lần kiểm này; log sạch + olean mới là bằng chứng đang có, không bịa exit code lịch sử. Những warning lint không yêu cầu compile lại.

Machine-readable audit: research/high_risk_20260910/worker_handoff_audit_20260912.json.
Script tái tính: scripts/audit_worker_handoff_20260912.py. Nó từ chối overwrite output cũ.

## 2. Đính chính cần giữ khi viết theorem/claim

1. S02 source dòng 30–32 viết `∀ eps ∃ family (large)` / `∃ eps ∀ family (large)`. Câu này không biểu diễn theorem đã compile. Phát biểu đúng là:
   - mỗi eps>0 có K(eps) chặn mọi family chuẩn hóa (normalized_dimension_le);
   - với mọi K có r,eps>0 sao cho chi_eps(F_r/r)>K;
   - vì vậy không có một eps>0 để dimension tăng vô hạn theo family.
   Dòng 24 cũng nói “trivial at any larger [tolerance]” quá rộng: staircase có dimension 1 khi eps >= 1/(2r), không phải vừa tăng eps từ 1/(4r) là đủ. Đây là lỗi prose, không phải lỗi theorem.
2. U03 dòng 41–43 và 256 nói “no lower bound”. Kết quả đúng loại trừ cận dưới tăng vô hạn theo obstruction order; cận dưới 1 vẫn có cho hai family unsafe. Nên viết “no diverging lower bound from obstruction order alone”.
3. D03 levels có điều kiện cardinality B: mức ở B cần |B|>=2; D6 k>=3 với |B|=k−1 đáp ứng. Không quảng bá bảng cho B singleton/empty ngoài hypotheses. Compensation cuối file chỉ giữ slope. Để có same-Q về cả hai mức còn phải định nghĩa centered gauge và prove mức Q.
4. Docstring BernoulliReferenceBridge cũ nói các slope chưa prove đã lỗi thời. Ghi note mới nối sang SlopeV1/SlopeBV1 và D03; không thay đổi source sạch chỉ vì docstring.
5. OPEN_ITEMS_CLOSURE_TARGETS_20260911.md có revision nhưng vẫn chứa hai bước sai nếu đọc thành proof: confidence sequence cho mu không tự suy continuity của w*(mu); window [s,s+w) không phải stopping time tại s. Dùng A06–A10 trong publication-gates thay cho hai shortcut đó.

## 3. F02: evidence thực và tiến trình

Dev artifact: research/confirm_ieee_20260912/functional_v4_lucb_dev_cellv1.json.
500 world = 100 instance × seeds 100–104; 8 policy = 4.000 run. Đã tính lại raw rows, censoring, paired key và world hash; tất cả khớp summaries. False-safe 0/4000 là số quan sát, không tự chứng minh xác suất lỗi bằng 0. Naive Top-k accuracy 0.098 so với 0.1; cả 10 Top-k sets xuất hiện.

| Policy | Certify | Median N (capped times, median ở dưới horizon) |
|---|---:|---:|
| C_lucb | 0.790 | 24364 |
| C_anytime | 0.748 | 35708 |
| C_extrema_oracle | 0.758 | 32052 |
| uniform | 0.564 | 93276 |

Paired C_lucb vs C_anytime: 374 cùng certify; 373 win / 1 loss; 21 chỉ lucb; 0 chỉ anytime; 105 neither. Conditional median ratio anytime/lucb = 1.345548. So với uniform: 282/282 win trong nhóm cùng certify; 113 chỉ lucb; 0 chỉ uniform. Các paired CI/p-value trong audit JSON là conditional-on-both-certify, không được biến thành unconditional dominance theorem.

Đọc code `_one_variant` và `_allocate_batch` xác nhận C_lucb dùng cùng CI/certificate, sigma ước lượng và observation streams; truth chỉ dùng hậu kiểm và oracle_extrema=None cho lucb. Source branch và flags raw đều không cấp true extrema/true sigma cho lucb. Luật chọn pair LUCB ở đây là implementation trong repo; audit này không khẳng định đã tái hiện nguyên một thuật toán có guarantee trong paper ngoài.

Panel chính ĐANG CHẠY lúc kiểm process: wrapper PID 55665, runner PID 55701; bắt đầu 2026-09-12T13:29:48Z; runner dùng khoảng 99% một CPU lúc snapshot ~10 phút. Freeze chính đã có, JSON kết quả chưa có. Không chạy thêm bản trùng, không kill và không sửa runner/import của nó. Không biết chính xác giờ hoàn thành. Dev 500 world mất 95 phút không phải ETA đã xác nhận cho panel chính 1000 world.

### Provenance: kết luận được và không được

- Dev artifact hash khớp freeze; runner hash đầu/cuối/current khớp ff9773028710408f81e5e9fb59533384231ab92744bc451f5ca85e49e361f795.
- Không suy từ đó rằng không file Python/dependency nào từng bị sửa trong toàn khoảng chạy. Hash endpoint không ghi lịch sử trung gian.
- Không chấp nhận lời “chỉ bốn file Lean làm source_changed=True” từ hai aggregate hash. source_fingerprint ở research_chains/provenance.py:74 hash git diff và TẤT CẢ untracked files. Chính dev JSON, manifest và freeze đều untracked và tham gia fingerprint. Chúng được tạo/thay đổi trong run. Vì vậy cờ này có thể đổi do output của run, không chỉ Lean. Không kết luận dữ liệu sai từ cờ đó.
- `CONFIRMATORY` trong admissibility_record chỉ kiểm tuple seeds. Manifest writer vẫn hard-code DEVELOPMENT_EMPIRICAL. Nhãn seed, identity protocol và preregistration là ba thứ khác nhau. Panel chính là comparison mới trên bộ seeds cũ đã dùng; muốn xác nhận một phương pháp tiếp tục tune sau kết quả này cần holdout mới, chốt trước.
- C_extrema_oracle là policy có thông tin thêm nhưng allocation heuristic riêng. Không có theorem nó là sample-complexity ceiling. Lucb thắng nó không mâu thuẫn với “thông tin thêm có thể hữu ích”; nó bác nhãn ceiling cho implementation này.
- Lượt audit hiện tại tạo script audit, JSON audit và chính note này khi panel chính đang chạy. Chúng có thể đổi whole-tree fingerprint. Không chỉnh runner v4, freeze runner hay research_chains/provenance.py trong lượt audit.

## 4. Gói giao worker — thứ tự thực hiện

### W1 — F02 hậu kiểm khi panel chính xong; làm độc lập với Lean

Input: main freeze và functional_v4_lucb_ieee10seed_cellv1.json sau khi xuất hiện.
Không khởi chạy lại. Chờ process hoàn tất và freeze có exit_code. Khi có kết quả:

```bash
cd /Users/phanan/cig-amf-main
python3 scripts/audit_worker_handoff_20260912.py --artifact research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json --out research/high_risk_20260910/f02_main_lucb_audit_20260912.json
```

Sau đó viết analysis MỚI: ghép key(seed,instance_id), kiểm world_sha với research/confirm_ieee_20260911/functional_v4_ieee10seed_cellv1.json; nếu world hash khác thì không gọi là cùng instance. Kiểm counts/output của các comparator cũ trên cùng world có tái lập khi chỉ thêm lucb không; giữ các khác biệt provenance/code thành giới hạn. Báo certificate fraction, capped median và CI có censoring, RMST-like, paired wins/losses/discordant certificates, false-safe, kết quả từng seed. Không ghép raw dev vào main. Không tune thêm vào seeds main sau khi xem.

Nghiệm thu: một script phân tích + JSON riêng với hashes, sample sizes/CI scope đầy đủ. Không chỉ đọc deployable_winner.

### W2 — F04/F05 full-extrema alternative: nên bắt đầu ngay trong lúc F02 chạy

Đây là ưu tiên Functional, không cần chờ baseline thua/thắng để bắt đầu.
Đọc LeanFunctionalPairFlipCostV1 và generator/certificate v4. PairFlip hiện chỉ unrestricted two-score calculation.

Phase đầu giới hạn R,K hữu hạn, K>=2, known independent Gaussian sigma_ra>0, sampling weights p_ra>0; true Top-k có strict gap. Đặt C_r(theta)=max_a theta_ra−min_a theta_ra. Với Top-k T thật, closed alternative là union theo i∈T,j∉T của C_i(lambda)<=C_j(lambda).

1. Prove union của các region lựa chọn argmin/argmax cho hai relation i,j bằng closed alternative; ties phải được phép thuộc nhiều region.
2. Trong mỗi region, ép min/max bằng các bất đẳng thức tuyến tính; capacity crossing tuyến tính. Prove inf KL trên full response table bằng minimum các bài toán QP region, các relation không thuộc pair có thể giữ nguyên.
3. Prove closure của strict wrong-answer alternatives trong lớp free-table và strict true gap; phân biệt minimum trên closed set với infimum trên strict reversal.
4. Dựng solver nhỏ R=2,K=3 trước: enumerate mọi region, verify primal feasibility và KKT/dual residual. Nếu gọi EXACT phải reconstruct rational witness + dual và kiểm bằng Fraction; solver float thành công không đủ. So với fixed-extrema formula, tìm một trường hợp optimizer đổi extrema và cost khác thật.

Outputs đề xuất, chưa tồn tại trong lượt audit: work/p13_conjectures/LeanFunctionalExtremaAlternativeV1.lean; scripts/run_functional_full_extrema_cost_v1.py; research/functional_extrema_20260912/.
Nghiệm thu: theorem set equality + theorem cost reduction, cùng small-panel numerical/exact certificate; không chỉ thay tên generic max-min game. Chưa đưa unknown sigma hoặc shared-F realizability vào theorem đầu; F06 là bước riêng. Weights bằng 0 cần infimum/coercivity xử lý riêng, không im lặng dùng theorem p>0.

Script run_functional_extremal_geometry_probe.py hiện import v3, thiếu C_lucb và giữ capacity order [1.4,1.2,1.0] theo relation index. Nếu tái dùng, tạo bản mới, randomize relation labels và giữ paired noise/outer gap; bản cũ không phải evidence đủ cho F04–F07.

### W3 — D04 trước, không prove lại đại số D05

Đọc D03, LeanD6ReferencePhaseValueV1, LeanD6ReferencePhaseThresholdV1 và D6_REFERENCE_PHASE_DERIVATION_20260911.md. Đã có 19+6 audit cho phần đại số. Chỗ mở là từ world thật đến các biến đại số, không phải equalizer 2×2.

D04a: với n=2k, k>=3, |A|=|T|=k, z∉A,T, B=others A z, định nghĩa actual centered gauge
F_(A,t)(x)=g_A(x)−E_t[g_A]+sum_i (rho*1_T(i)−s_i(t))*(x_i−t).
Prove cả hai mức Q_i(u)=rho*1_T(i)*(u−t), độc lập hidden A, và delta_square đúng điều kiện của construction. Đây là nghĩa vụ còn thiếu giữa compensation SLOPE và same-Q LEVEL. Không chỉ nhận same-Q làm hypothesis.

D04b: D=T\S, |S|=k, d=|D|, u=|A∩D|. Prove residual bằng explicit gate+linear cộng constant, rồi max/min có witness cube thật. Nối selectedRadius/productCompressionLoss với loss(d,u) trong derivation; xử lý d=0, d=1/u=0 riêng. Prove minimum trên mọi legal retained set bằng minimum trên feasible counts, gồm realizability của counts.

D05a sau D04: finite group averaging trên T/complement fixing z; worst-case risk không tăng; E[u]=h*d/k dưới orbit. D05b: instantiate dominance_gen/dominance_one, endpoint_max, phase_equalizers, weights_valid. Không tạo lại proof đại số đang sạch.

D06: transfer các hypotheses thực, nhất là (k−2)b>=1, t∈[0,1/2], rho∈[1,2], active/inactive và denominators. Threshold của phaseValueFull không tự là threshold của actual minimax trước D04/D05. Ngoài sufficient domain chỉ dùng general oscillation formula, chưa gọi full phase diagram.

Nghiệm thu: theorem trên actual F, actual residual và mọi legal decision; equality của minimax có cả primal upper/dual lower; không hidden WLOG premise, không axiom sound nhập khẩu. Compile file mới với receipt, print axioms.

### W4 — A06 rồi A07: một mắt nối adaptive có giới hạn rõ

Không giao “đóng toàn Gamma” trong một lệnh. Reuse LeanD6CyclicPhaseLawV1.estimate_law, MeanSquare, canonical path và dyadic union tools.

A06 target: với L_s=L0*2^s, v_s=|C|/(L_s*q^4), delta_s=delta/((s+1)(s+2)), prove
P(exists s, abs(muHat_s−mu)>sqrt(2*v_s*log(2/delta_s)))<=delta.
Derive marginal law trên actual common sample/path trước, không nhận hlaw/tail theorem chính làm giả thiết. Một q cố định nhưng công thức uniform theo q; không tuyên đồng thời mọi q nếu chưa union thêm. Dùng unclipped estimator nếu mu ngoài known interval; clipping chỉ bảo toàn bound khi mu thật nằm trong interval. Chưa dùng true phase để chọn estimator/stop.

A07 target: trực tiếp chặn Gamma(mu)−I(mu,wHat) bằng sai số estimate, optimization error và tracking error. Confidence sequence không tự cho ||w*(muHat)−w*(mu)||1; weights có thể nhảy ở boundary. Nếu dùng continuity/Lipschitz thì prove nó hoặc chọn value-level argument và ghi domain/alternative-set dependence.

A09/A10 sau đó: stopping adapted tại thời điểm có đủ dữ liệu, a.s. termination + tail đủ tích phân. Window [s,s+w) chỉ quan sát xong ở s+w−1; không gọi thời điểm bắt đầu window là stopping time. Discovery-only termination và settleIndex nhìn tương lai không đóng full algorithm. Benchmark cùng cyclic design không tự cho unrestricted Gamma.

### W5 — U04: chuyển separation thành tham số có dự đoán được chi phí

U03 đã xong; không thêm một wrapper khác chỉ đổi tên hai extreme families. Bước mới phải đưa cả safe-decision incompatibility và legal query partitions vào một bound tính được.

Bắt đầu bằng finite world/decision/query class trên selectedRadius thật: xây obstruction hypergraph, nêu mỗi query response loại bỏ/hạn chế world thế nào. Đề xuất một structural upper/lower có certificate hữu hạn; kiểm nó trả sparse=1 và dense=m−1, đồng thời ít nhất một family trung gian không được định nghĩa ngược từ optimal decision-tree depth. Reuse CardinalityQueryLaw cho các test đã có, không kể lại nó thành theorem mới.

Nghiệm thu nghiên cứu: định nghĩa không vòng tròn + chứng minh bound + actual-support instance vượt ngoài hai extreme + đối chiếu literature decision-region determination trước novelty claim. Nếu chỉ ra Bellman optimum/standard search complexity dưới tên mới, báo collision và đổi target. Không tự mở rộng zero-error depth sang noisy/expected complexity.

## 5. Điều phối đề nghị

Ngay bây giờ: giữ F02 đang chạy; giao W2 (Functional full extrema) và W3/D04a (D6 actual gauge) là hai việc cụ thể ưu tiên. W4/A06 là nhánh adaptive độc lập nếu còn worker. W5 là nhánh research tiếp theo của Support. S02 không cần worker compile lại; chỉ note đính chính prose. Nếu chỉ có một worker: W2 trước, W1 khi main hoàn tất, rồi W3. Có thể ưu tiên W3 trước W2 nếu mục tiêu gần nhất là static D6 submission.

Chưa có cơ sở từ audit này để nói cả sáu paper đã đủ novelty/publish. Structural S02 là sửa quantifier; U03 là separation có scope; Functional empirical headline đang bị baseline mạnh hơn; D6 static còn actual reduction; full adaptive Gamma vẫn mở. Query/MASTER không được audit lại trong lượt này, không nâng trạng thái dựa trên im lặng.
