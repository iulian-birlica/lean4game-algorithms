SHELL := /bin/bash

BOOTSTRAP := ./scripts/bootstrap-algorithmgame-deps.sh
GAME_DIR := Game
LEAN4GAME_DIR := vendor/lean4game
LEAN4GAME_NODE_MODULES := \
	$(LEAN4GAME_DIR)/node_modules \
	$(LEAN4GAME_DIR)/client/node_modules \
	$(LEAN4GAME_DIR)/relay/node_modules

.PHONY: install build clean

install:
	$(BOOTSTRAP)

build: install
	cd $(LEAN4GAME_DIR) && npm install
	cd $(GAME_DIR) && lake update -R -Klean4game.local
	cd $(GAME_DIR) && lake exe cache get
	cd $(GAME_DIR) && lake build
	cd $(LEAN4GAME_DIR) && npm run build:server
	cd $(LEAN4GAME_DIR) && npm run build:relay
	cd $(LEAN4GAME_DIR) && npm run build:client

clean:
	rm -rf $(LEAN4GAME_NODE_MODULES)
	@echo "Removed node_modules only; Lean build artifacts were left intact."
