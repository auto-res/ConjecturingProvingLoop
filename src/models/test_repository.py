from .repository import get_save_filepath

def test_get_save_filepath():
    dirpath = "/data/logs/regularopen"
    assert get_save_filepath(dirpath) == "/var/mathlib4/Mathlib/Logs/Regularopen.lean"