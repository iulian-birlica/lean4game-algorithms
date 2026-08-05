SHELL := /bin/bash

GAME_DIR := game

.PHONY: build clean

build:
	cd $(GAME_DIR) && lake update -R
	cd $(GAME_DIR) && lake exe cache get
	cd $(GAME_DIR) && lake build

clean:
	rm -rf $(GAME_DIR)/.lake $(GAME_DIR)/lake-packages
	@echo "Removed Lean build artifacts; dependencies will be re-resolved on the next build."
