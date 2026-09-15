import sys
sys.path.insert(0,'/Users/phanan/cig-amf-main')
sys.path.insert(0,'/Users/phanan/Documents/ChatGPT/CIG-AMF/work/code')
from envs.external.runtime import maybe_reexec_in_external_runtime
maybe_reexec_in_external_runtime(require_ready=True)
from envs.external.registry import build_environment
from run_query_signal_probe import delivery_opportunity
env=build_environment('rware',seed=8301,n_agents=5)
meta=delivery_opportunity(env,[1,2,3,4],8301)
print(meta,'rawgoals',env.raw_env.goals)
for a in env.raw_env.agents:print(a.id,a.x,a.y,a.dir,a.carrying_shelf)
snap=env.clone_state()
for i in meta['carrier_candidates']:
 env.restore_state(snap);acts=[0]*5;acts[i]=1
 print('step',acts,env.step(acts)[1:])
 print('carrier',env.raw_env.agents[i].x,env.raw_env.agents[i].y,env.raw_env.agents[i].carrying_shelf)
