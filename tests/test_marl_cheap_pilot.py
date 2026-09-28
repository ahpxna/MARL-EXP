import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import numpy as np
import torch
from scripts.MARL_cheap_pilot import evaluate, load_dataset, masks_from_logits


class Fixed:
    def __init__(self, output): self.output=torch.tensor(output,dtype=torch.float32)
    def __call__(self, *args): return self.output


class PilotTest(unittest.TestCase):
    def test_test_labels_do_not_select_nonoracle_outputs(self):
        m=3
        rows=[{'m':m,'episode_id':'holdout','t':1,'cached_queue_ranking':[0,1,2]}]
        nets={'score':Fixed([[3,2,1]]),'value':Fixed([[0,1,2,3,4,5,6,7]]),
              'direct':Fixed([[[1,3,2],[3,1,2]]])}
        args=(nets,torch.zeros((1,2)),torch.zeros((8,3)),torch.tensor([[1/3],[2/3]]))
        y=np.array([[0,1,4,0,2,6,7,0]],dtype=float)
        a,_,_=evaluate(rows,[0],y,*args)
        b,_,_=evaluate(rows,[0],-y,*args)
        pick=lambda rs:{(r['k'],r['method']):r['selected_mask'] for r in rs if not r['method'].startswith('oracle')}
        self.assertEqual(pick(a),pick(b))
        for r in a:
            self.assertEqual(r['selected_mask'].bit_count(),r['k'])
        self.assertTrue(any(r['gain_over_learned_prefix']<0 for r in b))

    def test_stable_direct_cardinality(self):
        logits=np.zeros((4,5))
        for k in range(1,5):
            masks=masks_from_logits(logits,k)
            self.assertTrue(all(int(s).bit_count()==k for s in masks))
            self.assertTrue(all(int(s)==(1<<k)-1 for s in masks))

    def test_dataset_hash_split_and_live_access_validation(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)
            def write(rows):
                with gzip.open(p/'tables.jsonl.gz','wt') as f:
                    for r in rows: f.write(json.dumps(r)+'\n')
                meta={'status':'COMPLETE','records':len(rows),
                      'table_sha256':hashlib.sha256((p/'tables.jsonl.gz').read_bytes()).hexdigest()}
                (p/'manifest.json').write_text(json.dumps(meta))
            rows=[dict(episode_id=f'e{i}',t=0,traffic_seed=i,split=s,m=2,
                       features=[0],values=[0,1,2,3],live_access_before={'oracle':0},
                       live_access_after={'oracle':0}) for i,s in enumerate(['train','val','test'])]
            write(rows); self.assertEqual(len(load_dataset(p)[1]),3)
            rows[2]['traffic_seed']=0; write(rows)
            with self.assertRaises(ValueError): load_dataset(p)
            rows[2]['traffic_seed']=2; rows[2]['live_access_after']['oracle']=1; write(rows)
            with self.assertRaises(ValueError): load_dataset(p)
            rows[2]['live_access_after']['oracle']=0; write(rows)
            with (p/'tables.jsonl.gz').open('ab') as f: f.write(b'bad')
            with self.assertRaises(ValueError): load_dataset(p)


if __name__=='__main__': unittest.main()
