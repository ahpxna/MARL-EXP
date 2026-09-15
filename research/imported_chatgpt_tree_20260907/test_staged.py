from pathlib import Path
import importlib.util,sys
sys.path.insert(0,'/Users/phanan/cig-amf-main')
import scripts
name='scripts.run_functional_variance_stopping_lab'
spec=importlib.util.spec_from_file_location(name,Path('work/code/run_functional_variance_stopping_lab.py'))
m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
import pytest
raise SystemExit(pytest.main(['-q','-p','no:cacheprovider','work/code/test_functional_allocation_v3.py','/Users/phanan/cig-amf-main/tests/test_functional_variance_stopping.py']))
