import numpy as np
import pytest
# Targets the v3 allocator explicitly.  The canonical name still holds v2, whose
# ordinal pilot/shrink allocator and driver-only anytime branch FAIL these tests
# by construction; v2 is kept intact so protocol-v2 artifacts stay reproducible.
from scripts.run_functional_variance_stopping_lab_v3 import _allocate_batch, run


def args(shape=(5,6)):
    means=np.zeros(shape);means[:, -1]=np.arange(1,shape[0]+1)
    return means,np.ones(shape),means-1,means+1


def test_shrink_changes_magnitudes_and_actual_allocation():
    # Same ordering; only relative magnitudes change. An ordinal allocator fails this.
    shape=(2,2);means,sigmas,lower,upper=args(shape)
    pilot=np.array([[.1,4.],[1.,2.]])
    shrink=np.sqrt(.5*pilot**2+.5*np.mean(pilot**2))
    assert np.array_equal(np.argsort(pilot.flat),np.argsort(shrink.flat))
    drivers=list(np.ndindex(shape))
    counts=[]
    for variant,scale in [('C_pilot',pilot),('C_shrink',shrink)]:
        n=np.full(shape,10)
        for _ in range(100):
            d=_allocate_batch(variant,16,means,sigmas,lower,upper,n,1,drivers,scale)
            assert d.sum()==16
            n+=d
        counts.append(n)
    assert not np.array_equal(*counts)
    assert counts[1][0,0]>counts[0][0,0]
    assert counts[1][0,1]<counts[0][0,1]


@pytest.mark.parametrize('variant',['C_anytime','C_known_sigma','C_pilot','C_shrink','C_split'])
@pytest.mark.parametrize('batch',[1,4,16,31])
def test_exploration_prevents_starvation_even_outside_driver_set(variant,batch):
    means,sigmas,lower,upper=args();n=np.full(means.shape,2)
    for _ in range(160):
        d=_allocate_batch(variant,batch,means,sigmas,lower,upper,n,2,[(0,0)],sigmas)
        assert np.all(d>=0) and d.sum()==batch
        n+=d
    # >= one exploration sample per batch: at least 160/30 levels, beyond the initial two.
    assert n.min()>=7


def test_uniform_remains_balanced_with_partial_batches():
    means,sigmas,lower,upper=args();n=np.full(means.shape,2)
    for batch in [16]*9+[7]:
        n+=_allocate_batch('uniform',batch,means,sigmas,lower,upper,n,2)
        assert n.max()-n.min()<=1


def test_diagnostics_and_invalid_batch():
    p=run(instances=1,seeds=(83,),relations=3,actions=4,topk=1,max_n=160,batch=8)
    for rows in p['runs_by_variant'].values():
        r=rows[0]
        assert r['true_topk_gap']>0
        assert r['minimum_cell_samples']==np.min(r['counts'])
        assert len(r['final_capacity_lower'])==3
        assert r['cells_at_initial_count']==int(np.sum(np.array(r['counts'])==np.array(r['initial_counts'])))
    with pytest.raises(ValueError,match='batch'):
        run(batch=0)
