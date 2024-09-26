import os

OPENAI_API_KEY = ''
REPLICATE_API_TOKEN = ''

# Options: meta/meta-llama-3-8b-instruct ; meta/meta-llama-70b-instruct
MODEL = 'gpt-3.5-turbo-0125'

# Path to opam installation, usually /home/username/.opam
# Replace username with your user name.
opam_path = '/home/username/.opam' 

# Path to parent directory of your coq projects (used for evaluation),
# we will use os.path.join(projects_path, proj_name) to locate the project.
# For example, the project you want to use for evaluation is /home/username/coq_projects/proj_name,
# then this should be '/home/username/data/coq_projects'.
projects_path = '/home/username/data/coq_projects'
data_path = './data'
eval_path = './evaluation'
proof_path = os.path.join(eval_path, 'proof')
