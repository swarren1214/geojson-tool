# GeoJSON State Splitter

Small MapLibre app for loading GeoJSON files, visualizing them on a map, and clipping polygon features to U.S. state boundaries.

## Features

- Import `.geojson` or `.json` files directly in the browser.
- Render points, lines, polygons, and multipolygons with MapLibre.
- Split polygon or multipolygon features that span multiple U.S. states.
- Compare original vs split output visually using styling on the map.

## Run

```bash
npm install
npm run dev
```

## Notes

- State boundaries come from the `us-atlas` dataset.
- Splitting uses polygon intersection against each state polygon.
- Non-polygon features are preserved unchanged.