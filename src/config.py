import os

OPENAI_API_KEY = ''
REPLICATE_API_TOKEN = ''
# Options: meta/meta-llama-3-8b-instruct ; meta/meta-llama-70b-instruct
MODEL = 'gpt-3.5-turbo-0125'

# Path to opam installation, usually /home/username/.opam
# Replace username with your user name.
opam_path = '/home/minghai/.opam' 

projects_path = '/home/minghai/data/coq_projects/test'
data_path = './data'
eval_path = './evaluation'
proof_path = os.path.join(eval_path, 'proof')
