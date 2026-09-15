# ============================================================================
# CIG-AMF  --  lenh chay 20260908  (moi dong la 1 lenh copy-paste doc lap)
# Thu tu quan trong: LEAN 1-2 truoc (khong phu thuoc gi), roi 3-4, roi EXP.
# ============================================================================

# --- LEAN 1: ba mat xich cua information limit (khong he co decide/native_decide)
cd /Users/phanan/cig-amf-main/work/p13_conjectures && LEAN_PATH="$PWD:$LEAN_PATH" lake env lean -o LeanD6InformationLimitV1.olean LeanD6InformationLimitV1.lean

# --- LEAN 2: audit 8 ten do -- phai ra [propext, Classical.choice, Quot.sound]
cd /Users/phanan/cig-amf-main/work/p13_conjectures && LEAN_PATH="$PWD:$LEAN_PATH" lake env lean AxiomAuditD6InformationLimitV1.lean

# --- LEAN 3: promotion native_decide -> kernel decide cho witness chi>=5 (10 theorem)
cd /Users/phanan/cig-amf-main/work/p13_conjectures && LEAN_PATH="$PWD:$LEAN_PATH" lake env lean -o LeanStructuralScalarChi5KernelV1.olean LeanStructuralScalarChi5KernelV1.lean

# --- LEAN 4: audit 10 ten do -- KHONG duoc co Lean.ofReduceBool
cd /Users/phanan/cig-amf-main/work/p13_conjectures && LEAN_PATH="$PWD:$LEAN_PATH" lake env lean AxiomAuditStructuralScalarChi5KernelV1.lean

# --- EXP 1: m=8 frontier tai mu=1/2 va 1  (du doan 6 va 4).  >165s trong VM cua tao -> CHAY NEN.
cd /Users/phanan/cig-amf-main && nohup python3 scripts/run_d6_margin_regret_frontier.py --m 8 --mu 1/2 1 --ansatz block --out research/d6/frontier_m8_mu_half_one_20260908.json > /tmp/m8_half_one.log 2>&1 &

# --- EXP 2: m=10, khe duy nhat cua <6,8>.  CHAY NEN, co log, dung doi.
cd /Users/phanan/cig-amf-main && nohup python3 scripts/run_d6_margin_regret_frontier.py --m 10 --mu 0 --ansatz block --out research/d6/frontier_m10_mu0_block_20260908.json > /tmp/m10_block.log 2>&1 &

# --- EXP 3: Functional v3, 300 instance x 3 seed (xac nhan 55-vs-0 co ben khong)
cd /Users/phanan/cig-amf-main && python3 scripts/run_functional_variance_stopping_lab_v3.py --instances 300 --seeds 8201 8202 8203 --out research/high_value_extensions/functional/variance_stopping_v3_300x3_20260908.json

# --- EXP 4: Query voi continuation policy KHONG phai NOOP (goc re cua 336 degenerate)
#     (can external_envs/runtime -- khong co trong VM cua tao, nen chi smoke-test duoc tren may may)
cd /Users/phanan/cig-amf-main && python3 scripts/run_external_query_transfer.py --adapter rware --seed 3001 --horizon 8 --discount 0.9 --continuation-policy forward --out research/external/query_transfer_h8_forward_20260908.json

# --- EXP 5: doi chung EXP4 -- cung h nhung policy noop, de tach nguyen nhan
cd /Users/phanan/cig-amf-main && python3 scripts/run_external_query_transfer.py --adapter rware --seed 3001 --horizon 8 --discount 0.9 --continuation-policy noop --out research/external/query_transfer_h8_noop_20260908.json

# --- Xem tien do 2 lenh chay nen:
tail -f /tmp/m8_half_one.log   # Ctrl-C de thoat, khong anh huong job
tail -f /tmp/m10_block.log
