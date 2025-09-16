import re
from typing import Optional
from dataclasses import dataclass
from pydantic import BaseModel, Field, field_validator


class Seed(BaseModel):
    pp: str = Field(default=str)

    @field_validator("pp")
    def validate_pp(cls, value: str):
        if not value.startswith("Mathlib"):
            raise ValueError("Invalid seed format")
        return value
    
    def __str__(self):
        return self.pp

    def __hash__(self):
        return hash(self.pp)

    @property
    def path(self) -> str:
        return "/var/mathlib4/" + self.pp.replace(".", "/") + ".lean"

class Conjecture(BaseModel):
    conjecture_id: str = Field(default="")
    header : str = Field(default="")
    informal_prefix : str = Field(default="")
    name: str = Field(default="")
    statement: str = Field(default="")
    grammatical: bool = Field(default=False)
    goal: str | None = Field(default=None)

    @field_validator("statement")
    def validate_statement(cls, value: str):
        if not re.match(r"^theorem.*:= by$", value, flags=re.DOTALL):
            raise ValueError("Invalid statement format")
        return value

    def __str__(self):
        return "\n\n".join([self.header, self.statement])

    def get_negative_conjecture(self) -> Optional["Conjecture"]:
        if  self.context is not None:
            return None

        tokens = self.statement.split(" ")
        theorem_name = " ".join(tokens[:2])
        content = " ".join(tokens[2:]).split(":=")[0]
        negated_statement = f"{theorem_name} ¬({content}) := by"
        return Conjecture(
            conjecture_id=self.conjecture_id,
            header = self.header,
            statement=negated_statement,
            grammatical=self.grammatical,
        )
    
    @property
    def sorry_str(self) -> str:
        return str(self) + " sorry"
    
    @property
    def exactmode(self) -> str:
        return str(self) + " exact?"
    
    @property
    def aesopmode(self) -> str:
        return str(self) + " aesop?"
    
    @classmethod
    def from_str(cls, conjecture_id: str, statement: str) -> "Conjecture":
        _, namespace_str, statement = statement.split("\n\n")
        namespaces = set(namespace_str.split(" ")[1:])
        return Conjecture(
            namespace=namespaces,
            conjecture_id=conjecture_id,
            statement=statement,
        )


@dataclass
class ConjectureEvalResult(object):
    conjecture : Conjecture
    already_exists : bool
    aesop_provable : bool
    interestingness : float = 0.0
    proof : str | None = None

    @property
    def header(self) -> str:
        return self.conjecture.header
    
    @property
    def name(self) -> str:
        return self.conjecture.name
    
    @property
    def statement(self) -> str:
        return self.conjecture.statement + "\n"

