from fastapi import FastAPI
from pydantic import BaseModel

from models import ConjectureGenerator, Seed

app = FastAPI()


class SeedModel(BaseModel):
    pp: str

class ConjectureRequest(BaseModel):
    idea: str
    seed: SeedModel

@app.post("/generate-conjectures")
def generate_conjectures(request: ConjectureRequest):
    generator = ConjectureGenerator()

    src_seed = Seed(pp=request.seed.pp)

    eval_results = generator.generated_by_idea_and_file(request.idea, src_seed)

    response_data = []
    for result in eval_results:
        response_data.append({
            "statement": str(result.conjecture),
            "grammatical": result.conjecture.grammatical,
            "aesop_provable": result.aesop_provable,
            "already_exists": result.already_exists,
            "proof": result.proof
        })

    return {"results": response_data}

if __name__ == "__main__":
    import uvicorn
    uvicorn.run("app:app", host="0.0.0.0", port=8000, reload=True)