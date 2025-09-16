import argparse

from models.repository import ProofRepository

def main(folderpath: str):
    repository = ProofRepository()
    repository.commit_succeeded_properties(folderpath)

if __name__ == "__main__":
    args = argparse.ArgumentParser()
    args.add_argument("--folderpath", type=str, default="/data/logs/RegularOpen", help="Directory name to commit.")
    
    folderpath = args.parse_args().folderpath
    
    main(folderpath)
