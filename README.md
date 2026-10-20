# RAILWORKS — Alpha 0.4

An original browser-based 3D isometric railway logistics and management prototype, inspired by railway gameplay in Factorio. The focus is railway building, trains, signals and a streamlined production economy.

## Play

[RAILWORKS on itch.io](https://gregclarke.itch.io/railworks)

## Project structure

- `web/index.html` — HTML entry point
- `web/styles.css` — UI styles
- `web/src/game.js` — railway, economy, rendering and control logic
- `.github/workflows/publish-itch.yml` — automated itch.io deployment via Butler

## Publishing

A push to `main` involving `web/**`, `VERSION` or the workflow triggers the automated deployment. The repository secret `BUTLER_API_KEY` must contain an itch.io API key authorized to publish to `gregclarke/railworks`. The GitHub Action pushes the `web/` directory to itch.io channel `html5` using the official Butler CLI. To publish on demand, run the workflow manually from the GitHub Actions tab.

After the first Butler push, set the new Butler upload as **This file will be played in the browser** in itch.io's Edit game page. Set project kind to **HTML** and keep the same channel for later updates.

## Controls

R — rail planner; J — turnout; B/C — block/chain signal; F — flip signal; H — railway blocks; V — train selection; T — new train; S — station; X — demolition; Q/E — camera rotation; Ctrl+Z — undo track construction.

## Save warning

Before changing builds, use the in-game Export Save option. This helps protect against browser-storage changes.

## Current limitations

The Alpha 0.4 track system has smoothed eight-direction curves and turnouts but does not yet reproduce every Factorio 2.0 rail component or signalling/interlocking rule. Head-on single-track deadlocks remain possible. The game uses native WebGL and has no external network runtime dependencies.
