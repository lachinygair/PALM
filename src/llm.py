from openai import OpenAI
import replicate
from .config import OPENAI_API_KEY, REPLICATE_API_TOKEN, MODEL
from .utils import *
import re


client = OpenAI(api_key=OPENAI_API_KEY)


system = 'You will be provided with a Coq proof state and related definitions and lemmas, your task is to give a proof.'

instruction = '''I will give you a Coq proof state, including both hypotheses and a specific goal and your need to prove it. Your response should be a singular code block of Coq proof starting with "```coq\n", ending with "Qed.```", without any additional explanation or commentary. Follow to these guidelines:
Introduce variables using unique names to avoid any conflicts.
Keep each command distinct and separated, avoid concatenations like ';' or '[cmd|cmd]'.
Organize your proof with bullets like '-', '+', and '*' instead of braces ({, }). Shift to their double symbols like '--' and '++', when necessary.
Effectively use given premises, follow the syntax and structure demonstrated in the examples provided.
'''

examples = '''
Example 1:

Hypotheses:
n, m: nat
IHn: m + n = n + m

Goal:
m + S n = S n + m

Your Response:
```coq
simpl. rewrite <- IHn. auto.
Qed.```

Example 2:
Hypotheses:

Goal:
forall n m : nat, m + n = n + m

Your Response:
```coq
intros n m. induction n.
- simpl. auto.
- simpl. rewrite <- IHn. auto.
Qed.```'''


def process_response(response: str):
    pattern = r'```coq\n(.*?)```'
    matches = re.findall(pattern, response, re.DOTALL)
    if matches:
        return matches[0]
    else:
        return response


def check_response(response: str):
    if not (response.startswith('```coq\n') and response.endswith('```')):
        return False
    return True


class LLM:
    def __init__(self, max_tokens=7168):
        self.max_tokens = max_tokens
        self.retry_limit = 2
        self.api_key: str
        self.history_query = []
        self.history_response = []
        self.messages = [
                {"role": "system", "content": system},
            ]
        self.length = [trim_prompt(p['content'])[0] for p in self.messages]

    
    def get_prompt(self, goals, premises, defs):
        prompt = instruction + examples
        assert goals != [], 'goals is [] before querying'
        
        goal = goals[0]
        prompt += '\n\nSolve This Proof State:\n\n'
        prompt += 'Hypotheses:\n{hypos}\n\nGoal:\n{goal}\n\n'\
                    .format(hypos='\n'.join([f'{k}: {v}' for k, v in goal['hypos'].items()]) if goal['hypos'] else 'None', goal=goal['goal'])
        if defs != [] or premises != []:
            prompt += 'Premises:'
        if defs != []:
            num_tokens = self.max_tokens - sum(self.length) - trim_prompt(prompt)[0]
            tokens_one = int(num_tokens/(len(defs)+len(premises)))
            prompt += '\n{defs}' \
                .format(defs= '\n'.join([trim_prompt(d, tokens_one)[1] for d in defs]))
        if premises != []:
            num_tokens = self.max_tokens - sum(self.length) - trim_prompt(prompt)[0]
            tokens_one = int(num_tokens/len(premises))
            prompt += '\n{lemmas}' \
                .format(lemmas= '\n'.join([trim_theorem(p, tokens_one)[1] for p in premises]))
        return prompt
    

    def query(self, prompt: str):
        if MODEL.startswith('gpt'):
            return self.query_gpt(prompt)
        elif 'llama' in MODEL:
            return self.query_llama(prompt)
        

    def query_llama(self, prompt: str):
        length, prompt = trim_prompt(prompt, self.max_tokens-sum(self.length))
        self.messages.append({'role': 'user', 'content': prompt})
        self.length.append(length)

        input = {
            "max_tokens": 1000,
            "min_tokens": 0,
            "temperature": 0.75,
            "system_prompt": system,
            "prompt": prompt,
            "prompt_template": "<|begin_of_text|><|start_header_id|>system<|end_header_id|>\n\nYou will be provided with a Coq proof state and related definitions and lemmas, your task is to give a proof.<|eot_id|><|start_header_id|>user<|end_header_id|>\n\n{prompt}<|eot_id|><|start_header_id|>assistant<|end_header_id|>\n\n",
            "length_penalty": 1,
            "stop_sequences": "<|end_of_text|>,<|eot_id|>",
            "presence_penalty": 1.15,
            "log_performance_metrics": False
        }

        output = replicate.run(
            MODEL,
            input=input
        )
        output = ''.join(output)
        print(output)
        self.messages.append({'role': 'assistant', 'content': output})
        return process_response(output)


    def query_gpt(self, prompt: str):
        length, prompt = trim_prompt(prompt, self.max_tokens-sum(self.length))
        self.messages.append({'role': 'user', 'content': prompt})
        self.length.append(length)
        # gpt-4o-2024-05-13
        response = client.chat.completions.create(model=MODEL,
            messages=self.messages)
        role = response.choices[0].message.role
        content = response.choices[0].message.content
        self.messages.append({'role': role, 'content': content})
        return process_response(content)
    

    def batch_record(self, custom_id, prompt):
        length, prompt = trim_prompt(prompt, self.max_tokens-sum(self.length))
        self.messages.append({'role': 'user', 'content': prompt})
        record = {
            "custom_id": custom_id, 
            "method": "POST", 
            "url": "/v1/chat/completions", 
            "body": {
                "model": "gpt-3.5-turbo-0125", 
                "messages": self.messages,
                "max_tokens": 1000
                }
            }
        return record


    def log(self):
        return self.messages[1:]
        

if __name__ == '__main__':
    pass
    
    
