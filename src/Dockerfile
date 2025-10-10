FROM python:3.11


WORKDIR /app
RUN pip install uv

COPY requirements.lock .
COPY pyproject.toml .

RUN uv sync

RUN curl -s -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh && \
    bash elan-init.sh -y && \
    rm -rf elan-init.sh
