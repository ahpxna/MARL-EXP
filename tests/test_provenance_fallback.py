from pathlib import Path

from research_chains.provenance import source_fingerprint


def test_source_fingerprint_works_without_git_and_ignores_research_outputs(tmp_path: Path):
    (tmp_path / "pkg").mkdir()
    (tmp_path / "pkg" / "a.py").write_text("x = 1\n", encoding="utf-8")
    first = source_fingerprint(tmp_path)
    assert first.startswith("TREE:")
    assert "UNAVAILABLE" not in first
    (tmp_path / "research").mkdir()
    (tmp_path / "research" / "result.json").write_text('{"value": 1}\n', encoding="utf-8")
    second = source_fingerprint(tmp_path)
    assert second == first
    (tmp_path / "pkg" / "a.py").write_text("x = 2\n", encoding="utf-8")
    third = source_fingerprint(tmp_path)
    assert third.startswith("TREE:") and third != first


def test_source_fingerprint_git_dirty_tree(tmp_path: Path):
    import subprocess
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, check=True)
    (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "a.py"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    clean = source_fingerprint(tmp_path)
    assert "+dirty:" not in clean and not clean.startswith("UNAVAILABLE")
    (tmp_path / "a.py").write_text("x = 2\n", encoding="utf-8")
    dirty = source_fingerprint(tmp_path)
    assert dirty.startswith(clean + "+dirty:")
