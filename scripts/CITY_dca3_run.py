#!/usr/bin/env python3
"""DCA3 audit correction. Versioned runner; does not modify the frozen DCA2 run.
Both reference and candidate scripts pass through this wrapper, so DCA3_END
applies equally. Original-author LayerNorm initialization is kept; transformed
observations use the author's nan_to_num and [-10,10] bound.
No performance panel is launched by importing this file.
"""
import hashlib, math, os, runpy, sys
from pathlib import Path
import numpy as np
import torch
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import scripts.CITY_eval4 as E4
from scripts.CITY_dcada_layer import TransformationLayer

def initial_params(ids):
    return {i:TransformationLayer().get_params_vector().clone() for i in ids}

class LightDCA3(E4.LightRLX):
    def __init__(self, info, policy, params):
        super().__init__(info,policy,adapter='raw')
        self.transforms={}
        for tid in info.tls:
            tr=TransformationLayer();tr.set_params_vector(torch.as_tensor(params[tid],dtype=torch.float32));tr.eval()
            self.transforms[tid]=tr
    def obs(self,tid):
        obs,halt,cur=super().obs(tid)
        with torch.no_grad():
            y=self.transforms[tid](torch.as_tensor(np.asarray(obs,np.float32))[None])[0]
            y=torch.clamp(torch.nan_to_num(y,nan=0.0,posinf=0.0,neginf=0.0),-10.0,10.0)
        return y.numpy().astype(np.float32),halt,cur

def install(end=None,params_path=None):
    if end is not None:
        assert math.isfinite(end) and end>0
    if params_path:
        params=torch.load(params_path,weights_only=False)
        build=E4.build_light
        def build_light(spec,info,adapter,box):
            net,light,a,b=build(spec,info,adapter,box)
            assert isinstance(light,E4.LightRLX),'DCA3 requires an RL signal'
            assert set(params)==set(info.tls),'controller ids'
            return net,LightDCA3(info,light.inner,params),a,b
        E4.build_light=build_light
    run0=E4.run
    def run(args,seed,requested_end):
        horizon=requested_end if end is None else end
        out=run0(args,seed,horizon)
        out['dca3_horizon_s']=horizon
        out['dca3_runner_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        out['dca3_params_sha256']=hashlib.sha256(Path(params_path).read_bytes()).hexdigest() if params_path else None
        return out
    E4.run=run

if __name__=='__main__':
    end=float(os.environ['DCA3_END']) if os.environ.get('DCA3_END') else None
    install(end,os.environ.get('DCA3_PARAMS'))
    target=sys.argv[1];sys.argv=[target]+sys.argv[2:]
    runpy.run_path(str(ROOT/target),run_name='__main__')
