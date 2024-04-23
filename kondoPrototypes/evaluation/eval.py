import csv
import os
from file_sloc import count_sloc_between

EVAL_PATH = os.path.dirname(os.path.realpath(__file__))
CSV_FILE = f"{EVAL_PATH}/protocols.csv"
ROOT_PATH = f"{EVAL_PATH}/.."
OUTPUT_PATH = f"{EVAL_PATH}/sloc.csv"

def analyze_protocol(file_path):
    with open(file_path, 'r') as csvfile:
        csv_reader = csv.reader(csvfile)
        res = []
        res.append("protocol,manual_proof,sync_spec,sync_proof,kondo_regular,kondo_proof_draft")

        for row in csv_reader:
            protocol = row[0]

            manual_proof = get_manual_proof_sloc(protocol)
            sync_proof = get_sync_proof_sloc(protocol)

            line = f"{protocol},{manual_proof},{sync_proof}"
            res.append(line)
    write_to_file(OUTPUT_PATH, "\n".join(res))

def get_manual_proof_sloc(protocol):
    manual_file_paths = [
        f"{ROOT_PATH}/{protocol}/manual/applicationProof.dfy",
        f"{ROOT_PATH}/{protocol}/manual/messageInvariants.dfy",
    ]
    manual_sloc = 0
    for fp in manual_file_paths:
        if os.path.isfile(fp):
            manual_sloc += count_sloc_between(fp, 1, 1000000)
        # else:
        #     print(f"{fp} not found")
    return manual_sloc

def get_sync_spec_sloc(protocol):
    spec_file_paths = [
        f"{ROOT_PATH}/{protocol}/hosts.dfy",
        f"{ROOT_PATH}/{protocol}/types.dfy",
        f"{ROOT_PATH}/{protocol}/sync/spec.dfy",
        f"{ROOT_PATH}/{protocol}/sync/system.dfy"
    ]
    spec_sloc = 0
    for fp in spec_file_paths:
        spec_sloc += count_sloc_between(fp, 1, 1000000)
    return spec_sloc

def get_sync_proof_sloc(protocol):
    sync_proof_file_path = f"{ROOT_PATH}/{protocol}/sync/applicationProof.dfy"
    sync_proof = count_sloc_between(sync_proof_file_path, 1, 1000000)
    return sync_proof

def get_kondo_regular_sloc(protocol):
    regular_file_paths = [
        f"{ROOT_PATH}/{protocol}/async-kondo/messageInvariantsAutogen.dfy",
        f"{ROOT_PATH}/{protocol}/async-kondo/monotonicityInvariantsAutogen.dfy",
        f"{ROOT_PATH}/{protocol}/async-kondo/ownershipInvariantsAutogen.dfy",
    ]
    regular_sloc = 0
    for fp in regular_file_paths:
        if os.path.isfile(fp):
            regular_sloc += count_sloc_between(fp, 1, 1000000)
    return regular_sloc

def get_kondo_proofdraft_sloc(protocol):
    kondo_proofdraft_file_path = f"{ROOT_PATH}/{protocol}/async-kondo/applicationProofDraftAutogen.dfy"
    # if file exists, then we compute SLOC
    if os.path.isfile(kondo_proofdraft_file_path):
        kondo_proofdraft_sloc = count_sloc_between(kondo_proofdraft_file_path, 1, 1000000)
    else:
        kondo_proofdraft_sloc = -1  # invalid
    return kondo_proofdraft_sloc


def write_to_file(file_path, content):
    with open(file_path, 'w') as file:
        file.write(content)


def main():
    analyze_protocol(CSV_FILE)

if __name__ == "__main__":
    main()