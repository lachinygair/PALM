# PALM: Proof Automation with Large Language Models

The source code and experiment scripts of the paper submitted to ASE 2024.

## Overview
```
PALM
 ├── study.jsonl            Errors recorded in formative study.
 ├── coq_projects/          Projcets in CoqGym.
 ├── data/                  Extracted data and config files.
 ├── evaluation/            Evaluation results.
 ├── src/                   Source code.
      ├── main.py           Entry point.
      ├── framework.py      Framework of PALM.
      ├── retrieval.py      Premise retrieval.
      ├── llm.py            Prompt and querying LLMs.
      ├── repair.py         Repair mechanisms.
      ├── proof_list.py     A list data structure to model a proof, and perform backtracking.
      ├── serapi.py         Interaction with Coq, modified from CoqGym.
      ├── config.py         Paths, LLM to use, and API keys.
      ├── extract_data.py   Extract theorem and proof data from projects.
      └── utils.py          Helper functions.             
```
## Installation
### Requirements
- [OPAM](https://opam.ocaml.org) 2.1.5
- [Anaconda Python](https://www.anaconda.com)
### Create conda environment
```
conda env create -f palm.yml && conda activate palm
```
### Build CoqGym Dataset
We use the testset of CoqGym, bulit with Coq 8.10, 8.11, and 8.12.
```
cd cd coq_projects

# Install switches for Coq 8.10, 8.11, and 8.12
./prepare.sh

# Build projects
./build.sh
```
### Install automated theorem provers used by CoqHammer
Please refer to [CoqHammer's document](https://coqhammer.github.io/#installation) for instaructions. You need to build the ATPs and add them to your PATH.

The data extracted from CoqGym is already in `data`, but you still need to build the projects. See next section if you want to run PALM on new projects not in CoqGym.

## (Optional) extract data from new projects
1. Build the project.
2. Add a new field of the options for Coq and switch used in `data/path.json`. Typically, we only need the options that map physical dirs to logical coqdirs (-Q and -R). You can find them in the `_CoqProject` file of that project. Some projects do not have `_CoqProject` file, you may find the options in their makefile.
3. Extract data by running:
    ```
    python -m src.extract_data --proj=projcet_name --threads=num_threads
    ```
    Extracted data will be written into `data/project_name`.

## Format of data extracted from CoqGym
This section describes the format of extracted data, from the projects in CoqGym or other projects.

We create a JSON file associted with a `.v` file (Coq source code) in the project. The directory and file structure of the project is kept. For example, `data/verdi/core/Net.json` includes data extracted from `coq_projects/verdi/core/Net.v`. The format of a JSON file is described below:
```
{
    "code": ["Require Import List.", ...],   # Parsed code in the file.
    "theorems": [                            # Extracted theorems and proofs.
        {
            "name": "permute",               # Name of the theorem.
            "kind": "Lemma",                 # "Theorem", "Lemma", "Example", etc.
            "begin": 16,                     # An index of the "code" list, beginning of the theorem.
            "end": 21                        # An index of the "code" lits, end of the theorem's proof.
        },
        ...
    ]
}
```

`data/intersection.json` enumerates all theorems used in our evaluation. Because we are using new Coq versions (8.10, 8.11 and 8.12) and Passport uses old version (8.9), some projects have different theorems. This file includes the theorems that exist in old and new versions.
 
`data/path.json` specifies the options for Coq and the switch used to run the project. 

## Run PALM
1. Set your openai API keys and the `opam` installation path in `src/config.py`. GPT-3.5 is used by default. See `src/llm.py` if you want other LLMs.
2. Run
    ```
    python -m src.main --proj="verdi" --exp_name="test" --threads=1 --resume="ours" -skip -backtrack -intersect
    ```
    The results are written in `./evaluation/proof/test`.
### Program Arguments
| Argument       | Description               | Required | Default |
|----------------|---------------------------|----------|---------|
| `--proj` | Specify the project to evaluate.|Yes| None|
| `--exp_name` | The name of this experiment for logging. |Yes|None|
| `--threads` | Number of threads. |No|1|
| `--theorem` | If specified, only evaluate this theorem.|No|None|
| `--resume` | Name of an experiment. If specified, will reuse proofs in that experiment, instead of querying LLMs.  | No | None |
| `-skip` | If set, skip the theorems that have evaluated in this experiment. (recommend to set) |No| False|
| `-backtrack` | If set, perform backtracking. (recommend to set) |No| False |
| `-intersect` | If set, only run the theorems in `data/intersection.json`. (recommend to set when running evaluation, not to set when running new projects) |No| False |

## Format of experiment logs
We create a JSON file for each theorem to record the proof process. For example, `evaluation/proof/ours/verdi/core/Net.json/RT1n_step.json` is the log for the `RT1n_step` theorem in `coq_project/verdi/core/Net.v`. The format of a JSON file is described below:
```
[       # Multiple records if run the experiment multiple times, without setting "-skip".
    {                       
        "history": {                # Proof process
            "proof": "...",         # Generated proof. Meaningful only if "succ" is true.
            "exceptions": [         # Errors encountered during the proof
                {
                    "ctx": ["intros a."],       # Tactics applied before the error happens.
                    "tactic": "intros a.",      # Tactic that causes the error.
                    "exn": "..."      ,         # Error message.
                    "type": "used_var"          # Type of the error.
                }
            ],
            
        },
        "chat": [                   # Conversation with LLM.
            {                   
                "role": "user",     # "user" or "assistant" (LLM)
                "content": "...",
            },
            ...
        ]
        "original": "intros a. intros a. ...",  # The original proof, either from LLM's response, or resumed from another experiment, if "--resume" is specified.
        "succ": true                            # If the proof is sccessful. 
    }
]
``` 
