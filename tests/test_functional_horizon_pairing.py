"""Guard the experimental coupling needed for horizon comparisons."""
import numpy as np
import pytest
from scripts.run_functional_variance_stopping_lab_v3 import _instance_data, _draw_world, _prefix_stats
from scripts.analyze_functional_censoring_pairing import median_interval, restricted_time


@pytest.mark.parametrize('instance_id', [0, 1, 99])
def test_world_and_each_cell_prefix_are_horizon_invariant(instance_id):
    small=_instance_data(8301,instance_id,5,6,31,'instance_cell_v1')
    large=_instance_data(8301,instance_id,5,6,59,'instance_cell_v1')
    for i in (0,1):
        np.testing.assert_array_equal(small[i],large[i])
    np.testing.assert_array_equal(small[2],large[2][:,:,:31])
    assert small[3]==large[3]
    other=_instance_data(8301,instance_id+1,5,6,31,'instance_cell_v1')
    assert small[3]!=other[3]


def test_legacy_generation_keeps_rng_consumption_order():
    a=np.random.default_rng(42);b=np.random.default_rng(42)
    for i in range(3):
        truth,sigma=_draw_world(a,3,4)
        noise=a.normal(truth[:,:,None],sigma[None,:,None],size=(3,4,21))
        generated=_instance_data(42,i,3,4,21,'legacy_sequential',b)
        for x,y in zip((truth,sigma,noise),generated[:3]):
            np.testing.assert_array_equal(x,y)


def test_short_stream_cannot_silently_certify():
    with pytest.raises(AssertionError,match='stream exhausted'):
        _prefix_stats(np.zeros((2,2,5)),np.full((2,2),4),offset=2)


def test_censoring_does_not_confuse_zero_with_missing():
    assert restricted_time({'N_certificate':0},100)==0
    assert restricted_time({'N_certificate':None},100)==100
    assert median_interval([1,2])['order_indices']==[0,3]
    assert median_interval(range(300))['order_indices']==[133,168]
    assert median_interval(range(163))['order_indices']==[69,95]
