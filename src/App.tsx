import { useEffect, useMemo, useRef, useState, type MouseEvent as ReactMouseEvent, type ReactNode } from 'react';
import maplibregl, { GeoJSONSource, LngLatBoundsLike, Map } from 'maplibre-gl';
import { AnimatePresence, motion } from 'framer-motion';
import booleanPointInPolygon from '@turf/boolean-point-in-polygon';
import type { Feature, GeoJsonProperties, Geometry, LineString, MultiPolygon, Point, Polygon } from 'geojson';
import {
  Braces,
  Check,
  ChevronDown,
  ChevronUp,
  Download,
  FileUp,
  FolderTree,
  Loader2,
  MapPinned,
  Merge,
  Plus,
  Pencil,
  PenLine,
  Redo2,
  Scissors,
  Tag,
  Trash2,
  Undo2,
  X,
} from 'lucide-react';
import type { AnyFeatureCollection } from './types';
import {
  getCollectionBounds,
  mergePolygons,
  parseGeoJson,
  separatePolygonParts,
  smoothPolygonFeature,
  smoothPolygonsInCollection,
  type SmoothAlgorithm,
  splitPolygonsByStates,
} from './lib/geojson';
import { getEmptyStateBoundaries, getStateBoundaries } from './lib/stateBoundaries';

const EMPTY_COLLECTION: AnyFeatureCollection = {
  type: 'FeatureCollection',
  features: [],
};

const BASEMAP_STYLE = 'https://basemaps.cartocdn.com/gl/voyager-gl-style/style.json';
const POLYGON_FILL_COLOR = '#2a9d8f';
const POLYGON_SELECTED_FILL_COLOR = '#f59e0b';
const POLYGON_HOVER_FILL_COLOR = '#0f172a';
const CSV_INSIDE_COLOR = '#16a34a';
const CSV_OUTSIDE_COLOR = '#dc2626';
const CSV_MIXED_CLUSTER_COLOR = '#facc15';
const SMOOTH_PANEL_WIDTH_PX = 288;
const SMOOTH_PANEL_VIEWPORT_MARGIN_PX = 16;
const SMOOTH_PANEL_ESTIMATED_HEIGHT_PX = 420;
const POLYGON_EDIT_OUTLINE_SOURCE_ID = 'polygon-edit-outline';
const POLYGON_EDIT_VERTICES_SOURCE_ID = 'polygon-edit-vertices';
const POLYGON_EDIT_SNAP_POINT_SOURCE_ID = 'polygon-edit-snap-point';
const POLYGON_EDIT_SNAP_SEGMENT_SOURCE_ID = 'polygon-edit-snap-segment';
const POLYGON_EDIT_OUTLINE_LAYER_ID = 'polygon-edit-outline-layer';
const POLYGON_EDIT_VERTICES_LAYER_ID = 'polygon-edit-vertices-layer';
const POLYGON_EDIT_SNAP_POINT_LAYER_ID = 'polygon-edit-snap-point-layer';
const POLYGON_EDIT_SNAP_SEGMENT_LAYER_ID = 'polygon-edit-snap-segment-layer';
const POLYGON_EDIT_SNAP_THRESHOLD_PX = 10;
const POLYGON_DRAW_PREVIEW_SOURCE_ID = 'polygon-draw-preview';
const POLYGON_DRAW_FILL_LAYER_ID = 'polygon-draw-fill-layer';
const POLYGON_DRAW_LINE_LAYER_ID = 'polygon-draw-line-layer';
const POLYGON_DRAW_VERTICES_LAYER_ID = 'polygon-draw-vertices-layer';
const WORKSPACE_DB_NAME = 'geojson-tool-workspace';
const WORKSPACE_DB_VERSION = 1;
const WORKSPACE_STORE_NAME = 'workspace';
const WORKSPACE_SNAPSHOT_KEY = 'current';

type PolygonBoundaryIndexItem = {
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>;
  minLon: number;
  minLat: number;
  maxLon: number;
  maxLat: number;
};

type PolygonVertexReference = {
  polygonIndex: number;
  ringIndex: number;
  coordIndex: number;
};

type PolygonSegmentReference = {
  polygonIndex: number;
  ringIndex: number;
  segmentIndex: number;
};

type PolygonSnapResult = {
  coordinate: [number, number];
  kind: 'none' | 'vertex' | 'edge';
  segment?: [[number, number], [number, number]];
};

function clonePolygonFeatureGeometry(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
): Feature<Polygon | MultiPolygon, GeoJsonProperties> {
  if (feature.geometry.type === 'Polygon') {
    return {
      ...feature,
      geometry: {
        ...feature.geometry,
        coordinates: feature.geometry.coordinates.map((ring) => ring.map(([lng, lat]) => [lng, lat])),
      },
    };
  }

  return {
    ...feature,
    geometry: {
      ...feature.geometry,
      coordinates: feature.geometry.coordinates.map((polygon) =>
        polygon.map((ring) => ring.map(([lng, lat]) => [lng, lat])),
      ),
    },
  };
}

function getPolygonRings(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
): Array<{ polygonIndex: number; ringIndex: number; ring: number[][] }> {
  if (feature.geometry.type === 'Polygon') {
    return feature.geometry.coordinates.map((ring, ringIndex) => ({
      polygonIndex: 0,
      ringIndex,
      ring,
    }));
  }

  return feature.geometry.coordinates.flatMap((polygon, polygonIndex) =>
    polygon.map((ring, ringIndex) => ({ polygonIndex, ringIndex, ring })),
  );
}

function buildPolygonVertexCollection(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
): AnyFeatureCollection {
  const vertexFeatures: Feature<Point, GeoJsonProperties>[] = [];

  getPolygonRings(feature).forEach(({ polygonIndex, ringIndex, ring }) => {
    if (ring.length < 2) {
      return;
    }

    const uniqueVertexCount = Math.max(0, ring.length - 1);
    for (let coordIndex = 0; coordIndex < uniqueVertexCount; coordIndex++) {
      const coordinate = ring[coordIndex];
      if (!coordinate || coordinate.length < 2) {
        continue;
      }

      const vertexId = `${polygonIndex}:${ringIndex}:${coordIndex}`;
      vertexFeatures.push({
        type: 'Feature',
        geometry: {
          type: 'Point',
          coordinates: [coordinate[0], coordinate[1]],
        },
        properties: {
          vertexId,
          polygonIndex,
          ringIndex,
          coordIndex,
        },
      });
    }
  });

  return {
    type: 'FeatureCollection',
    features: vertexFeatures,
  };
}

function updatePolygonVertexCoordinate(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  reference: PolygonVertexReference,
  coordinate: [number, number],
): Feature<Polygon | MultiPolygon, GeoJsonProperties> {
  if (feature.geometry.type === 'Polygon') {
    const nextCoordinates = feature.geometry.coordinates.map((ring) => ring.map(([lng, lat]) => [lng, lat]));
    const ring = nextCoordinates[reference.ringIndex];
    if (!ring) {
      return feature;
    }

    ring[reference.coordIndex] = [coordinate[0], coordinate[1]];
    if (reference.coordIndex === 0 && ring.length > 1) {
      ring[ring.length - 1] = [coordinate[0], coordinate[1]];
    }

    return {
      ...feature,
      geometry: {
        ...feature.geometry,
        coordinates: nextCoordinates,
      },
    };
  }

  const nextCoordinates = feature.geometry.coordinates.map((polygon) =>
    polygon.map((ring) => ring.map(([lng, lat]) => [lng, lat])),
  );
  const ring = nextCoordinates[reference.polygonIndex]?.[reference.ringIndex];
  if (!ring) {
    return feature;
  }

  ring[reference.coordIndex] = [coordinate[0], coordinate[1]];
  if (reference.coordIndex === 0 && ring.length > 1) {
    ring[ring.length - 1] = [coordinate[0], coordinate[1]];
  }

  return {
    ...feature,
    geometry: {
      ...feature.geometry,
      coordinates: nextCoordinates,
    },
  };
}

function findNearestVertexForCoordinate(
  map: Map,
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  coordinate: [number, number],
  maxDistancePx = 16,
): { reference: PolygonVertexReference; vertexId: string } | null {
  const targetPoint = map.project([coordinate[0], coordinate[1]]);
  let bestMatch: { reference: PolygonVertexReference; vertexId: string } | null = null;
  let bestDistance = maxDistancePx;

  getPolygonRings(feature).forEach(({ polygonIndex, ringIndex, ring }) => {
    const uniqueVertexCount = Math.max(0, ring.length - 1);
    for (let coordIndex = 0; coordIndex < uniqueVertexCount; coordIndex++) {
      const vertex = ring[coordIndex];
      const projected = map.project([vertex[0], vertex[1]]);
      const dx = projected.x - targetPoint.x;
      const dy = projected.y - targetPoint.y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= bestDistance) {
        bestDistance = distance;
        bestMatch = {
          reference: { polygonIndex, ringIndex, coordIndex },
          vertexId: `${polygonIndex}:${ringIndex}:${coordIndex}`,
        };
      }
    }
  });

  return bestMatch;
}

function findNearestSegmentForCoordinate(
  map: Map,
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  coordinate: [number, number],
  maxDistancePx = POLYGON_EDIT_SNAP_THRESHOLD_PX,
): { reference: PolygonSegmentReference; snappedCoordinate: [number, number] } | null {
  const targetPoint = map.project([coordinate[0], coordinate[1]]);
  let bestMatch: { reference: PolygonSegmentReference; snappedCoordinate: [number, number] } | null = null;
  let bestDistance = maxDistancePx;

  getPolygonRings(feature).forEach(({ polygonIndex, ringIndex, ring }) => {
    for (let segmentIndex = 0; segmentIndex < ring.length - 1; segmentIndex++) {
      const start = ring[segmentIndex];
      const end = ring[segmentIndex + 1];
      const startProjected = map.project([start[0], start[1]]);
      const endProjected = map.project([end[0], end[1]]);
      const segmentDx = endProjected.x - startProjected.x;
      const segmentDy = endProjected.y - startProjected.y;
      const segmentLengthSquared = segmentDx * segmentDx + segmentDy * segmentDy;
      if (segmentLengthSquared === 0) {
        continue;
      }

      const projectionRatio =
        ((targetPoint.x - startProjected.x) * segmentDx + (targetPoint.y - startProjected.y) * segmentDy) /
        segmentLengthSquared;
      const t = Math.max(0, Math.min(1, projectionRatio));
      const snappedX = startProjected.x + segmentDx * t;
      const snappedY = startProjected.y + segmentDy * t;
      const dx = snappedX - targetPoint.x;
      const dy = snappedY - targetPoint.y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= bestDistance) {
        bestDistance = distance;
        const snappedLngLat = map.unproject([snappedX, snappedY]);
        bestMatch = {
          reference: {
            polygonIndex,
            ringIndex,
            segmentIndex,
          },
          snappedCoordinate: [snappedLngLat.lng, snappedLngLat.lat],
        };
      }
    }
  });

  return bestMatch;
}

function getSegmentCoordinates(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  reference: PolygonSegmentReference,
): [[number, number], [number, number]] | null {
  const rings = getPolygonRings(feature);
  const ring = rings.find(
    (candidate) =>
      candidate.polygonIndex === reference.polygonIndex && candidate.ringIndex === reference.ringIndex,
  )?.ring;
  if (!ring) {
    return null;
  }

  const start = ring[reference.segmentIndex];
  const end = ring[reference.segmentIndex + 1];
  if (!start || !end) {
    return null;
  }

  return [
    [start[0], start[1]],
    [end[0], end[1]],
  ];
}

function insertPolygonVertexOnSegment(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  reference: PolygonSegmentReference,
  coordinate: [number, number],
): Feature<Polygon | MultiPolygon, GeoJsonProperties> {
  if (feature.geometry.type === 'Polygon') {
    const nextCoordinates = feature.geometry.coordinates.map((ring) => ring.map(([lng, lat]) => [lng, lat]));
    const ring = nextCoordinates[reference.ringIndex];
    if (!ring) {
      return feature;
    }

    ring.splice(reference.segmentIndex + 1, 0, [coordinate[0], coordinate[1]]);
    return {
      ...feature,
      geometry: {
        ...feature.geometry,
        coordinates: nextCoordinates,
      },
    };
  }

  const nextCoordinates = feature.geometry.coordinates.map((polygon) =>
    polygon.map((ring) => ring.map(([lng, lat]) => [lng, lat])),
  );
  const ring = nextCoordinates[reference.polygonIndex]?.[reference.ringIndex];
  if (!ring) {
    return feature;
  }

  ring.splice(reference.segmentIndex + 1, 0, [coordinate[0], coordinate[1]]);
  return {
    ...feature,
    geometry: {
      ...feature.geometry,
      coordinates: nextCoordinates,
    },
  };
}

function removePolygonVertex(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  reference: PolygonVertexReference,
): Feature<Polygon | MultiPolygon, GeoJsonProperties> {
  if (feature.geometry.type === 'Polygon') {
    const nextCoordinates = feature.geometry.coordinates.map((ring) => ring.map(([lng, lat]) => [lng, lat]));
    const ring = nextCoordinates[reference.ringIndex];
    if (!ring) {
      return feature;
    }

    const uniqueVertices = ring.slice(0, -1);
    if (uniqueVertices.length <= 3 || reference.coordIndex >= uniqueVertices.length) {
      return feature;
    }

    uniqueVertices.splice(reference.coordIndex, 1);
    if (uniqueVertices.length < 3) {
      return feature;
    }

    nextCoordinates[reference.ringIndex] = [...uniqueVertices, [...uniqueVertices[0]]];
    return {
      ...feature,
      geometry: {
        ...feature.geometry,
        coordinates: nextCoordinates,
      },
    };
  }

  const nextCoordinates = feature.geometry.coordinates.map((polygon) =>
    polygon.map((ring) => ring.map(([lng, lat]) => [lng, lat])),
  );
  const ring = nextCoordinates[reference.polygonIndex]?.[reference.ringIndex];
  if (!ring) {
    return feature;
  }

  const uniqueVertices = ring.slice(0, -1);
  if (uniqueVertices.length <= 3 || reference.coordIndex >= uniqueVertices.length) {
    return feature;
  }

  uniqueVertices.splice(reference.coordIndex, 1);
  if (uniqueVertices.length < 3) {
    return feature;
  }

  nextCoordinates[reference.polygonIndex][reference.ringIndex] = [...uniqueVertices, [...uniqueVertices[0]]];
  return {
    ...feature,
    geometry: {
      ...feature.geometry,
      coordinates: nextCoordinates,
    },
  };
}

function snapCoordinateToNearbyGeometry(
  map: Map,
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  coordinate: [number, number],
  movingReference: PolygonVertexReference,
): PolygonSnapResult {
  const targetPoint = map.project([coordinate[0], coordinate[1]]);
  let bestCoordinate: [number, number] = coordinate;
  let bestDistance = POLYGON_EDIT_SNAP_THRESHOLD_PX;
  let snapKind: PolygonSnapResult['kind'] = 'none';
  let snapSegment: [[number, number], [number, number]] | undefined;

  getPolygonRings(feature).forEach(({ polygonIndex, ringIndex, ring }) => {
    if (ring.length < 2) {
      return;
    }

    const uniqueVertexCount = Math.max(0, ring.length - 1);
    for (let coordIndex = 0; coordIndex < uniqueVertexCount; coordIndex++) {
      if (
        polygonIndex === movingReference.polygonIndex &&
        ringIndex === movingReference.ringIndex &&
        coordIndex === movingReference.coordIndex
      ) {
        continue;
      }

      const vertex = ring[coordIndex];
      const projected = map.project([vertex[0], vertex[1]]);
      const dx = projected.x - targetPoint.x;
      const dy = projected.y - targetPoint.y;
      const distance = Math.sqrt(dx * dx + dy * dy);
      if (distance <= bestDistance) {
        bestDistance = distance;
        bestCoordinate = [vertex[0], vertex[1]];
        snapKind = 'vertex';
        snapSegment = undefined;
      }
    }

    for (let segmentIndex = 0; segmentIndex < ring.length - 1; segmentIndex++) {
      // Do not snap against the segments directly adjacent to the vertex being moved.
      if (polygonIndex === movingReference.polygonIndex && ringIndex === movingReference.ringIndex) {
        const uniqueVertexCount = Math.max(0, ring.length - 1);
        const previousSegmentIndex =
          movingReference.coordIndex === 0 ? Math.max(0, uniqueVertexCount - 1) : movingReference.coordIndex - 1;
        const nextSegmentIndex = movingReference.coordIndex;
        if (segmentIndex === previousSegmentIndex || segmentIndex === nextSegmentIndex) {
          continue;
        }
      }

      const start = ring[segmentIndex];
      const end = ring[segmentIndex + 1];
      const startProjected = map.project([start[0], start[1]]);
      const endProjected = map.project([end[0], end[1]]);
      const segmentDx = endProjected.x - startProjected.x;
      const segmentDy = endProjected.y - startProjected.y;
      const segmentLengthSquared = segmentDx * segmentDx + segmentDy * segmentDy;
      if (segmentLengthSquared === 0) {
        continue;
      }

      const projectionRatio =
        ((targetPoint.x - startProjected.x) * segmentDx + (targetPoint.y - startProjected.y) * segmentDy) /
        segmentLengthSquared;
      const t = Math.max(0, Math.min(1, projectionRatio));
      const snappedX = startProjected.x + segmentDx * t;
      const snappedY = startProjected.y + segmentDy * t;
      const edgeDx = snappedX - targetPoint.x;
      const edgeDy = snappedY - targetPoint.y;
      const edgeDistance = Math.sqrt(edgeDx * edgeDx + edgeDy * edgeDy);

      if (edgeDistance <= bestDistance) {
        bestDistance = edgeDistance;
        const snappedLngLat = map.unproject([snappedX, snappedY]);
        bestCoordinate = [snappedLngLat.lng, snappedLngLat.lat];
        snapKind = 'edge';
        snapSegment = [
          [start[0], start[1]],
          [end[0], end[1]],
        ];
      }
    }
  });

  return {
    coordinate: bestCoordinate,
    kind: snapKind,
    segment: snapSegment,
  };
}

function getPolygonGeometryBounds(geometry: Polygon | MultiPolygon): [number, number, number, number] {
  let minLon = Number.POSITIVE_INFINITY;
  let minLat = Number.POSITIVE_INFINITY;
  let maxLon = Number.NEGATIVE_INFINITY;
  let maxLat = Number.NEGATIVE_INFINITY;

  const rings = geometry.type === 'Polygon' ? geometry.coordinates : geometry.coordinates.flat();
  rings.forEach((ring) => {
    ring.forEach(([lon, lat]) => {
      minLon = Math.min(minLon, lon);
      minLat = Math.min(minLat, lat);
      maxLon = Math.max(maxLon, lon);
      maxLat = Math.max(maxLat, lat);
    });
  });

  return [minLon, minLat, maxLon, maxLat];
}

function buildPolygonBoundaryIndex(data: AnyFeatureCollection): PolygonBoundaryIndexItem[] {
  return data.features.flatMap((feature) => {
    if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
      return [];
    }

    const polygonFeature = feature as Feature<Polygon | MultiPolygon, GeoJsonProperties>;
    const [minLon, minLat, maxLon, maxLat] = getPolygonGeometryBounds(polygonFeature.geometry);

    return [
      {
        feature: polygonFeature,
        minLon,
        minLat,
        maxLon,
        maxLat,
      },
    ];
  });
}

function withCsvBoundaryStatus(
  csvData: AnyFeatureCollection,
  polygonBoundaryIndex: PolygonBoundaryIndexItem[],
): AnyFeatureCollection {
  if (!csvData.features.length) {
    return csvData;
  }

  let changed = false;

  const features = csvData.features.map((feature) => {
    if (feature.geometry?.type !== 'Point') {
      return feature;
    }

    const [lon, lat] = feature.geometry.coordinates;
    if (!Number.isFinite(lon) || !Number.isFinite(lat)) {
      return feature;
    }

    const insideGeoJsonBoundary = polygonBoundaryIndex.some((boundary) => {
      if (lon < boundary.minLon || lon > boundary.maxLon || lat < boundary.minLat || lat > boundary.maxLat) {
        return false;
      }

      return booleanPointInPolygon(feature as Feature<Point, GeoJsonProperties>, boundary.feature);
    });

    const previousValue = feature.properties?.insideGeoJsonBoundary === true;
    if (previousValue === insideGeoJsonBoundary) {
      return feature;
    }

    changed = true;
    return {
      ...feature,
      properties: {
        ...feature.properties,
        insideGeoJsonBoundary,
      },
    };
  });

  if (!changed) {
    return csvData;
  }

  return {
    ...csvData,
    features,
  };
}

function getClassifiedCsvPointData(
  csvData: AnyFeatureCollection,
  polygonBoundaryIndex: PolygonBoundaryIndexItem[],
): AnyFeatureCollection {
  return withCsvBoundaryStatus(csvData, polygonBoundaryIndex);
}

function getPolygonColorForId(appFeatureId: string): string {
  // Hash the feature id into a stable hue so each polygon keeps its own color.
  let hash = 0;
  for (let i = 0; i < appFeatureId.length; i++) {
    hash = (hash << 5) - hash + appFeatureId.charCodeAt(i);
    hash |= 0;
  }

  const hue = Math.abs(hash) % 360;
  return `hsl(${hue} 62% 58%)`;
}

function buildPolygonColorById(data: AnyFeatureCollection): Record<string, string> {
  const colorById: Record<string, string> = {};
  const usedHueBuckets = new Set<number>();

  data.features.forEach((feature, index) => {
    if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const appFeatureId = feature.properties?.appFeatureId;
    if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
      return;
    }

    let hue = Math.abs(
      appFeatureId.split('').reduce((acc, char) => ((acc << 5) - acc + char.charCodeAt(0)) | 0, index),
    ) % 360;
    let bucket = Math.floor(hue / 8);

    // Spread neighboring IDs apart so split siblings do not collapse into the same visible color.
    while (usedHueBuckets.has(bucket)) {
      hue = (hue + 137) % 360;
      bucket = Math.floor(hue / 8);
    }

    usedHueBuckets.add(bucket);
    colorById[appFeatureId] = `hsl(${hue} 62% 58%)`;
  });

  return colorById;
}

function withPolygonColors(
  data: AnyFeatureCollection,
  colorById: Record<string, string>,
): AnyFeatureCollection {
  return {
    ...data,
    features: data.features.map((feature) => {
      if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
        return feature;
      }

      const appFeatureId = feature.properties?.appFeatureId;
      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return feature;
      }

      return {
        ...feature,
        properties: {
          ...feature.properties,
          polygonColor: colorById[appFeatureId] || getPolygonColorForId(appFeatureId),
        },
      };
    }),
  };
}

function waitForUiPaint(): Promise<void> {
  return new Promise((resolve) => {
    window.requestAnimationFrame(() => resolve());
  });
}

function parseCsvRows(rawText: string): string[][] {
  const rows: string[][] = [];
  let row: string[] = [];
  let cell = '';
  let inQuotes = false;

  for (let i = 0; i < rawText.length; i++) {
    const char = rawText[i];

    if (char === '"') {
      const isEscapedQuote = inQuotes && rawText[i + 1] === '"';
      if (isEscapedQuote) {
        cell += '"';
        i += 1;
      } else {
        inQuotes = !inQuotes;
      }
      continue;
    }

    if (char === ',' && !inQuotes) {
      row.push(cell.trim());
      cell = '';
      continue;
    }

    if ((char === '\n' || char === '\r') && !inQuotes) {
      if (char === '\r' && rawText[i + 1] === '\n') {
        i += 1;
      }

      row.push(cell.trim());
      cell = '';

      if (row.some((value) => value !== '')) {
        rows.push(row);
      }

      row = [];
      continue;
    }

    cell += char;
  }

  row.push(cell.trim());
  if (row.some((value) => value !== '')) {
    rows.push(row);
  }

  return rows;
}

function parseCsvPointCollection(rawText: string, fileName: string, fileId: string): {
  data: AnyFeatureCollection;
  importedCount: number;
  skippedCount: number;
} {
  const rows = parseCsvRows(rawText);
  if (!rows.length) {
    throw new Error('CSV is empty.');
  }

  const normalizedHeader = rows[0].map((value) => value.trim().toLowerCase());
  const latHeaderNames = new Set(['lat', 'latitude', 'y']);
  const lonHeaderNames = new Set(['lon', 'lng', 'long', 'longitude', 'x']);

  const latHeaderIndex = normalizedHeader.findIndex((value) => latHeaderNames.has(value));
  const lonHeaderIndex = normalizedHeader.findIndex((value) => lonHeaderNames.has(value));
  const hasHeader = latHeaderIndex >= 0 && lonHeaderIndex >= 0;

  const latIndex = hasHeader ? latHeaderIndex : 0;
  const lonIndex = hasHeader ? lonHeaderIndex : 1;

  if (!hasHeader && rows[0].length < 2) {
    throw new Error('CSV must include lat/lon columns or at least two coordinate columns.');
  }

  const features: Feature<Point, GeoJsonProperties>[] = [];
  let skippedCount = 0;
  const startRow = hasHeader ? 1 : 0;

  for (let i = startRow; i < rows.length; i++) {
    const row = rows[i];
    const latValue = row[latIndex];
    const lonValue = row[lonIndex];

    const lat = typeof latValue === 'string' ? Number.parseFloat(latValue) : Number.NaN;
    const lon = typeof lonValue === 'string' ? Number.parseFloat(lonValue) : Number.NaN;

    if (!Number.isFinite(lat) || !Number.isFinite(lon) || lat < -90 || lat > 90 || lon < -180 || lon > 180) {
      skippedCount += 1;
      continue;
    }

    features.push({
      type: 'Feature',
      geometry: {
        type: 'Point',
        coordinates: [lon, lat],
      },
      properties: {
        csvSourceFileId: fileId,
        csvSourceFile: fileName,
        csvRowNumber: i + 1,
      },
    });
  }

  if (!features.length) {
    throw new Error('No valid coordinates found in CSV.');
  }

  return {
    data: {
      type: 'FeatureCollection',
      features,
    },
    importedCount: features.length,
    skippedCount,
  };
}

type UploadedFileMeta = {
  id: string;
  name: string;
  featureCount: number;
  polygonCount: number;
};

type CsvPointFileMeta = {
  id: string;
  name: string;
  pointCount: number;
};

type ContextMenuState = {
  open: boolean;
  x: number;
  y: number;
  appFeatureId: string | null;
  nameDraft: string;
};

type PolygonListItem = {
  appFeatureId: string;
  sourceFileId: string;
  sourceFileName: string;
  defaultName: string;
  isMultiPolygon: boolean;
  stateName?: string;
  stateBadge?: string;
  splitByState: boolean;
};

type SmoothPanelState = {
  open: boolean;
  appFeatureId: string | null;
  algorithm: SmoothAlgorithm;
  sensitivity: number;
  x: number;
  y: number;
};

type PolygonGeometryEditState = {
  open: boolean;
  appFeatureId: string | null;
  draftFeature: Feature<Polygon | MultiPolygon, GeoJsonProperties> | null;
  draggingVertexId: string | null;
  snapCoordinate: [number, number] | null;
  snapSegment: [[number, number], [number, number]] | null;
  snapKind: 'none' | 'vertex' | 'edge';
};

type PolygonDrawState = {
  open: boolean;
  sourceFileId: string | null;
  sourceFileName: string;
  coordinates: [number, number][];
  cursorCoordinate: [number, number] | null;
};

type WorkspaceSnapshot = {
  displayData: AnyFeatureCollection;
  csvPointData: AnyFeatureCollection;
  csvPointFiles: CsvPointFileMeta[];
  uploadedFiles: UploadedFileMeta[];
  polygonNames: Record<string, string>;
};

function openWorkspaceDatabase(): Promise<IDBDatabase> {
  return new Promise((resolve, reject) => {
    if (typeof window === 'undefined' || !('indexedDB' in window)) {
      reject(new Error('IndexedDB is not available.'));
      return;
    }

    const request = window.indexedDB.open(WORKSPACE_DB_NAME, WORKSPACE_DB_VERSION);

    request.onupgradeneeded = () => {
      const database = request.result;
      if (!database.objectStoreNames.contains(WORKSPACE_STORE_NAME)) {
        database.createObjectStore(WORKSPACE_STORE_NAME);
      }
    };

    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error ?? new Error('Could not open workspace database.'));
  });
}

async function loadPersistedWorkspaceSnapshot(): Promise<WorkspaceSnapshot | null> {
  const database = await openWorkspaceDatabase();

  return new Promise((resolve, reject) => {
    const transaction = database.transaction(WORKSPACE_STORE_NAME, 'readonly');
    const store = transaction.objectStore(WORKSPACE_STORE_NAME);
    const request = store.get(WORKSPACE_SNAPSHOT_KEY);

    request.onsuccess = () => resolve((request.result as WorkspaceSnapshot | undefined) ?? null);
    request.onerror = () => reject(request.error ?? new Error('Could not read persisted workspace.'));
    transaction.oncomplete = () => database.close();
    transaction.onerror = () => reject(transaction.error ?? new Error('Could not read persisted workspace.'));
  });
}

async function savePersistedWorkspaceSnapshot(snapshot: WorkspaceSnapshot): Promise<void> {
  const database = await openWorkspaceDatabase();

  return new Promise((resolve, reject) => {
    const transaction = database.transaction(WORKSPACE_STORE_NAME, 'readwrite');
    const store = transaction.objectStore(WORKSPACE_STORE_NAME);
    store.put(snapshot, WORKSPACE_SNAPSHOT_KEY);

    transaction.oncomplete = () => {
      database.close();
      resolve();
    };
    transaction.onerror = () => reject(transaction.error ?? new Error('Could not persist workspace.'));
  });
}

async function clearPersistedWorkspaceSnapshot(): Promise<void> {
  const database = await openWorkspaceDatabase();

  return new Promise((resolve, reject) => {
    const transaction = database.transaction(WORKSPACE_STORE_NAME, 'readwrite');
    const store = transaction.objectStore(WORKSPACE_STORE_NAME);
    store.delete(WORKSPACE_SNAPSHOT_KEY);

    transaction.oncomplete = () => {
      database.close();
      resolve();
    };
    transaction.onerror = () => reject(transaction.error ?? new Error('Could not clear persisted workspace.'));
  });
}

function isWorkspaceSnapshotEmpty(snapshot: WorkspaceSnapshot): boolean {
  return (
    snapshot.displayData.features.length === 0 &&
    snapshot.csvPointData.features.length === 0 &&
    snapshot.csvPointFiles.length === 0 &&
    snapshot.uploadedFiles.length === 0 &&
    Object.keys(snapshot.polygonNames).length === 0
  );
}

type GeometryMetrics = {
  vertices: number;
  edges: number;
};

type ToolbarActionButtonProps = {
  onClick: () => void;
  disabled: boolean;
  ariaLabel: string;
  tooltip: string;
  className: string;
  children: ReactNode;
};

type PolygonIconActionButtonProps = {
  onClick: (event: ReactMouseEvent<HTMLButtonElement>) => void;
  ariaLabel: string;
  tooltip: string;
  className: string;
  disabled?: boolean;
  children: ReactNode;
};

type OperationAlertState = {
  type: 'success' | 'error';
  message: string;
};

const MAX_HISTORY_ENTRIES = 100;

function sanitizeFileName(value: string): string {
  const trimmed = value.trim();
  if (!trimmed) {
    return 'polygon';
  }

  return trimmed
    .replace(/[^a-zA-Z0-9-_ ]+/g, '')
    .replace(/\s+/g, '-')
    .replace(/-+/g, '-')
    .toLowerCase();
}

const STATE_NAME_TO_CODE: Record<string, string> = {
  Alabama: 'AL',
  Alaska: 'AK',
  Arizona: 'AZ',
  Arkansas: 'AR',
  California: 'CA',
  Colorado: 'CO',
  Connecticut: 'CT',
  Delaware: 'DE',
  'District of Columbia': 'DC',
  Florida: 'FL',
  Georgia: 'GA',
  Hawaii: 'HI',
  Idaho: 'ID',
  Illinois: 'IL',
  Indiana: 'IN',
  Iowa: 'IA',
  Kansas: 'KS',
  Kentucky: 'KY',
  Louisiana: 'LA',
  Maine: 'ME',
  Maryland: 'MD',
  Massachusetts: 'MA',
  Michigan: 'MI',
  Minnesota: 'MN',
  Mississippi: 'MS',
  Missouri: 'MO',
  Montana: 'MT',
  Nebraska: 'NE',
  Nevada: 'NV',
  'New Hampshire': 'NH',
  'New Jersey': 'NJ',
  'New Mexico': 'NM',
  'New York': 'NY',
  'North Carolina': 'NC',
  'North Dakota': 'ND',
  Ohio: 'OH',
  Oklahoma: 'OK',
  Oregon: 'OR',
  Pennsylvania: 'PA',
  'Rhode Island': 'RI',
  'South Carolina': 'SC',
  'South Dakota': 'SD',
  Tennessee: 'TN',
  Texas: 'TX',
  Utah: 'UT',
  Vermont: 'VT',
  Virginia: 'VA',
  Washington: 'WA',
  'West Virginia': 'WV',
  Wisconsin: 'WI',
  Wyoming: 'WY',
};

function getStateCodeLabel(stateName: string | undefined): string | undefined {
  if (typeof stateName !== 'string') {
    return undefined;
  }

  const normalizedName = stateName.trim();
  if (!normalizedName) {
    return undefined;
  }

  return STATE_NAME_TO_CODE[normalizedName] || normalizedName;
}

function getPolygonDefaultName(feature: Feature<Geometry, GeoJsonProperties>, index: number): string {
  const fromProp = feature.properties?.polygonName;
  if (typeof fromProp === 'string' && fromProp.trim()) {
    return fromProp.trim();
  }

  const stateName = feature.properties?.stateName;
  if (typeof stateName === 'string' && stateName.trim()) {
    return `State Piece: ${stateName.trim()}`;
  }

  return `Polygon ${index + 1}`;
}

function annotateImportedCollection(data: AnyFeatureCollection, fileId: string, fileName: string): AnyFeatureCollection {
  return {
    ...data,
    features: data.features.map((feature, index) => ({
      ...feature,
      properties: {
        ...feature.properties,
        sourceFileId: fileId,
        sourceFileName: fileName,
        sourceFeatureIndex: index,
        appFeatureId: `feature-${fileId}-${Date.now()}-${index}`,
      },
    })),
  };
}

function withFeatureIds(data: AnyFeatureCollection, prefix: string): AnyFeatureCollection {
  const seen = new Set<string>();
  const runStamp = Date.now();

  return {
    ...data,
    features: data.features.map((feature, index) => {
      const existingId = feature.properties?.appFeatureId;
      const normalizedExistingId =
        typeof existingId === 'string' && existingId.trim() ? existingId.trim() : null;

      const appFeatureId =
        normalizedExistingId && !seen.has(normalizedExistingId)
          ? normalizedExistingId
          : `${prefix}-${runStamp}-${index}-${Math.random().toString(36).slice(2, 8)}`;

      seen.add(appFeatureId);

      return {
        ...feature,
        properties: {
          ...feature.properties,
          appFeatureId,
        },
      };
    }),
  };
}

function buildPolygonDrawPreviewCollection(drawState: PolygonDrawState): AnyFeatureCollection {
  if (!drawState.open) {
    return EMPTY_COLLECTION;
  }

  const features: Feature<Geometry, GeoJsonProperties>[] = [];
  const coordinates = drawState.coordinates;

  if (coordinates.length >= 3) {
    features.push({
      type: 'Feature',
      geometry: {
        type: 'Polygon',
        coordinates: [[...coordinates, [...coordinates[0]]]],
      },
      properties: {
        preview: true,
      },
    });
  }

  const lineCoordinates = drawState.cursorCoordinate
    ? [...coordinates, drawState.cursorCoordinate]
    : [...coordinates];
  if (lineCoordinates.length >= 2) {
    features.push({
      type: 'Feature',
      geometry: {
        type: 'LineString',
        coordinates: lineCoordinates,
      } as LineString,
      properties: {
        preview: true,
      },
    });
  }

  coordinates.forEach((coordinate, index) => {
    features.push({
      type: 'Feature',
      geometry: {
        type: 'Point',
        coordinates: [coordinate[0], coordinate[1]],
      },
      properties: {
        vertexIndex: index,
      },
    });
  });

  return {
    type: 'FeatureCollection',
    features,
  };
}

function isPolygonFeature(feature: Feature<Geometry, GeoJsonProperties>): boolean {
  return feature.geometry?.type === 'Polygon' || feature.geometry?.type === 'MultiPolygon';
}

function countFeatureGeometryMetrics(
  feature: Feature<Geometry, GeoJsonProperties> | undefined,
): GeometryMetrics {
  if (!feature || !isPolygonFeature(feature)) {
    return { vertices: 0, edges: 0 };
  }

  let vertices = 0;
  let edges = 0;

  const countRing = (ring: number[][]) => {
    if (!Array.isArray(ring) || ring.length < 2) {
      return;
    }

    const first = ring[0];
    const last = ring[ring.length - 1];
    const isClosed = first[0] === last[0] && first[1] === last[1];
    const ringVertices = isClosed ? Math.max(0, ring.length - 1) : ring.length;

    vertices += ringVertices;
    edges += ringVertices > 1 ? (isClosed ? ringVertices : ringVertices - 1) : 0;
  };

  if (feature.geometry.type === 'Polygon') {
    const polygonFeature = feature as Feature<Polygon, GeoJsonProperties>;
    polygonFeature.geometry.coordinates.forEach((ring) => countRing(ring));
    return { vertices, edges };
  }

  const multiPolygonFeature = feature as Feature<MultiPolygon, GeoJsonProperties>;
  multiPolygonFeature.geometry.coordinates.forEach((polygon) => {
    polygon.forEach((ring) => countRing(ring));
  });

  return { vertices, edges };
}

function ToolbarActionButton({
  onClick,
  disabled,
  ariaLabel,
  tooltip,
  className,
  children,
}: ToolbarActionButtonProps) {
  return (
    <div className="group relative flex-1 min-w-0">
      <button onClick={onClick} disabled={disabled} aria-label={ariaLabel} title={tooltip} className={className}>
        {children}
      </button>
      <span
        role="tooltip"
        className="pointer-events-none absolute -top-2 left-1/2 z-20 -translate-x-1/2 -translate-y-full whitespace-nowrap rounded-md bg-slate-900 px-2 py-1 text-[11px] font-semibold text-white opacity-0 shadow-sm transition group-hover:opacity-100 group-focus-within:opacity-100"
      >
        {tooltip}
      </span>
    </div>
  );
}

function PolygonIconActionButton({
  onClick,
  ariaLabel,
  tooltip,
  className,
  disabled = false,
  children,
}: PolygonIconActionButtonProps) {
  return (
    <div className="group relative">
      <button
        onClick={onClick}
        title={tooltip}
        aria-label={ariaLabel}
        disabled={disabled}
        className={`${className} ${disabled ? 'cursor-not-allowed opacity-50' : ''}`}
      >
        {children}
      </button>
      <span
        role="tooltip"
        className="pointer-events-none absolute -top-1 left-1/2 z-20 -translate-x-1/2 -translate-y-full whitespace-nowrap rounded-md bg-slate-900 px-2 py-1 text-[10px] font-semibold text-white opacity-0 shadow-sm transition group-hover:opacity-100 group-focus-within:opacity-100"
      >
        {tooltip}
      </span>
    </div>
  );
}

export default function App() {
  const mapContainerRef = useRef<HTMLDivElement | null>(null);
  const fileInputRef = useRef<HTMLInputElement | null>(null);
  const mapRef = useRef<Map | null>(null);

  const [displayData, setDisplayData] = useState<AnyFeatureCollection>(EMPTY_COLLECTION);
  const [csvPointData, setCsvPointData] = useState<AnyFeatureCollection>(EMPTY_COLLECTION);
  const [csvPointFiles, setCsvPointFiles] = useState<CsvPointFileMeta[]>([]);
  const [uploadedFiles, setUploadedFiles] = useState<UploadedFileMeta[]>([]);
  const [error, setError] = useState<string>('');
  const [isDragOverUpload, setIsDragOverUpload] = useState<boolean>(false);
  const [isHandlingUploads, setIsHandlingUploads] = useState<boolean>(false);
  const [uploadStatusMessage, setUploadStatusMessage] = useState<string>('');
  const [isRestoringWorkspace, setIsRestoringWorkspace] = useState<boolean>(true);
  const [isMapStyleReady, setIsMapStyleReady] = useState<boolean>(false);
  const [showStates, setShowStates] = useState<boolean>(false);
  const [isSplittingAll, setIsSplittingAll] = useState<boolean>(false);
  const [splittingFeatureIds, setSplittingFeatureIds] = useState<Set<string>>(new Set());
  const [operationAlert, setOperationAlert] = useState<OperationAlertState | null>(null);
  const [isCsvLegendExpanded, setIsCsvLegendExpanded] = useState<boolean>(false);
  const [collapsedPolygonIds, setCollapsedPolygonIds] = useState<Set<string>>(new Set());
  const [polygonNames, setPolygonNames] = useState<Record<string, string>>({});
  const [editingPolygonId, setEditingPolygonId] = useState<string | null>(null);
  const [editingPolygonNameDraft, setEditingPolygonNameDraft] = useState<string>('');
  const [savingPolygonEditId, setSavingPolygonEditId] = useState<string | null>(null);
  const [mergeMode, setMergeMode] = useState<boolean>(false);
  const [selectedForMerge, setSelectedForMerge] = useState<Set<string>>(new Set());
  const [selectedFeatureId, setSelectedFeatureId] = useState<string | null>(null);
  const [undoStack, setUndoStack] = useState<WorkspaceSnapshot[]>([]);
  const [redoStack, setRedoStack] = useState<WorkspaceSnapshot[]>([]);
  const [smoothPanel, setSmoothPanel] = useState<SmoothPanelState>({
    open: false,
    appFeatureId: null,
    algorithm: 'chaikin',
    sensitivity: 40,
    x: 0,
    y: 0,
  });
  const [polygonGeometryEdit, setPolygonGeometryEdit] = useState<PolygonGeometryEditState>({
    open: false,
    appFeatureId: null,
    draftFeature: null,
    draggingVertexId: null,
    snapCoordinate: null,
    snapSegment: null,
    snapKind: 'none',
  });
  const [polygonDraw, setPolygonDraw] = useState<PolygonDrawState>({
    open: false,
    sourceFileId: null,
    sourceFileName: '',
    coordinates: [],
    cursorCoordinate: null,
  });
  const [contextMenu, setContextMenu] = useState<ContextMenuState>({
    open: false,
    x: 0,
    y: 0,
    appFeatureId: null,
    nameDraft: '',
  });

  const displayDataRef = useRef<AnyFeatureCollection>(displayData);
  const csvPointDataRef = useRef<AnyFeatureCollection>(csvPointData);
  const showStatesRef = useRef<boolean>(showStates);
  const polygonNameByIdRef = useRef<Record<string, string>>({});
  const hoveredFeatureIdRef = useRef<string | null>(null);
  const selectedFeatureIdRef = useRef<string | null>(null);
  const pendingFitBoundsRef = useRef<LngLatBoundsLike | null>(null);
  const uploadDragDepthRef = useRef<number>(0);
  const polygonColorByIdRef = useRef<Record<string, string>>({});
  const hasRestoredWorkspaceRef = useRef<boolean>(false);
  const polygonGeometryEditRef = useRef<PolygonGeometryEditState>(polygonGeometryEdit);
  const polygonDrawRef = useRef<PolygonDrawState>(polygonDraw);
  const draggingVertexRef = useRef<PolygonVertexReference | null>(null);
  const suppressNextMapClickRef = useRef<boolean>(false);

  function createWorkspaceSnapshot(): WorkspaceSnapshot {
    return {
      displayData,
      csvPointData,
      csvPointFiles,
      uploadedFiles,
      polygonNames,
    };
  }

  function applyWorkspaceSnapshot(snapshot: WorkspaceSnapshot) {
    setDisplayData(snapshot.displayData);
    setCsvPointData(snapshot.csvPointData);
    setCsvPointFiles(snapshot.csvPointFiles);
    setUploadedFiles(snapshot.uploadedFiles);
    setPolygonNames(snapshot.polygonNames);
    setMergeMode(false);
    setSelectedForMerge(new Set());
    closeContextMenu();
    closePolygonMenu();
    closeSmoothPanel();
    closePolygonGeometryEdit();
    closePolygonDraw();
    setError('');

    const map = mapRef.current;
    if (map) {
      clearHoveredFeature(map);
      clearSelectedFeature(map);
    }
  }

  function recordHistorySnapshot(snapshot = createWorkspaceSnapshot()) {
    setUndoStack((previous) => [...previous.slice(-(MAX_HISTORY_ENTRIES - 1)), snapshot]);
    setRedoStack([]);
  }

  function handleUndo() {
    if (!undoStack.length) {
      return;
    }

    const previous = undoStack[undoStack.length - 1];
    setUndoStack((stack) => stack.slice(0, -1));
    setRedoStack((stack) => [...stack, createWorkspaceSnapshot()]);
    applyWorkspaceSnapshot(previous);
  }

  function handleRedo() {
    if (!redoStack.length) {
      return;
    }

    const next = redoStack[redoStack.length - 1];
    setRedoStack((stack) => stack.slice(0, -1));
    setUndoStack((stack) => [...stack.slice(-(MAX_HISTORY_ENTRIES - 1)), createWorkspaceSnapshot()]);
    applyWorkspaceSnapshot(next);
  }

  function shouldIgnoreHistoryShortcut(target: EventTarget | null): boolean {
    if (!(target instanceof HTMLElement)) {
      return false;
    }

    const tagName = target.tagName.toLowerCase();
    return target.isContentEditable || tagName === 'input' || tagName === 'textarea' || tagName === 'select';
  }

  function closeContextMenu() {
    setContextMenu({
      open: false,
      x: 0,
      y: 0,
      appFeatureId: null,
      nameDraft: '',
    });
  }

  function closePolygonMenu() {
    // Polygon actions are rendered inline on each card, so no menu state is needed.
  }

  function closeSmoothPanel() {
    setSmoothPanel((previous) => ({
      ...previous,
      open: false,
      appFeatureId: null,
    }));
  }

  function fitMapToBounds(bounds: LngLatBoundsLike) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    if (!map.isStyleLoaded()) {
      pendingFitBoundsRef.current = bounds;
      return;
    }

    pendingFitBoundsRef.current = null;
    map.fitBounds(bounds, {
      padding: 48,
      duration: 700,
    });
  }

  function fitMapToCollection(data: AnyFeatureCollection) {
    const bounds = getCollectionBounds(data);
    if (bounds) {
      fitMapToBounds(bounds as LngLatBoundsLike);
    }
  }

  function syncCsvPointSource(
    csvData: AnyFeatureCollection,
    boundaryIndex: PolygonBoundaryIndexItem[] = polygonBoundaryIndex,
  ) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    const csvSource = map.getSource('csv-point-data') as GeoJSONSource | undefined;
    csvSource?.setData(getClassifiedCsvPointData(csvData, boundaryIndex));
  }

  function syncPolygonGeometryEditSources(editState: PolygonGeometryEditState = polygonGeometryEditRef.current) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    const outlineSource = map.getSource(POLYGON_EDIT_OUTLINE_SOURCE_ID) as GeoJSONSource | undefined;
    const verticesSource = map.getSource(POLYGON_EDIT_VERTICES_SOURCE_ID) as GeoJSONSource | undefined;
    const snapPointSource = map.getSource(POLYGON_EDIT_SNAP_POINT_SOURCE_ID) as GeoJSONSource | undefined;
    const snapSegmentSource = map.getSource(POLYGON_EDIT_SNAP_SEGMENT_SOURCE_ID) as GeoJSONSource | undefined;
    if (!outlineSource || !verticesSource || !snapPointSource || !snapSegmentSource) {
      return;
    }

    if (!editState.open || !editState.draftFeature) {
      outlineSource.setData(EMPTY_COLLECTION);
      verticesSource.setData(EMPTY_COLLECTION);
      snapPointSource.setData(EMPTY_COLLECTION);
      snapSegmentSource.setData(EMPTY_COLLECTION);
      return;
    }

    outlineSource.setData({
      type: 'FeatureCollection',
      features: [editState.draftFeature],
    });
    verticesSource.setData(buildPolygonVertexCollection(editState.draftFeature));

    if (editState.snapCoordinate) {
      snapPointSource.setData({
        type: 'FeatureCollection',
        features: [
          {
            type: 'Feature',
            geometry: {
              type: 'Point',
              coordinates: [editState.snapCoordinate[0], editState.snapCoordinate[1]],
            },
            properties: {
              kind: editState.snapKind,
            },
          },
        ],
      });
    } else {
      snapPointSource.setData(EMPTY_COLLECTION);
    }

    if (editState.snapSegment) {
      snapSegmentSource.setData({
        type: 'FeatureCollection',
        features: [
          {
            type: 'Feature',
            geometry: {
              type: 'LineString',
              coordinates: [
                [editState.snapSegment[0][0], editState.snapSegment[0][1]],
                [editState.snapSegment[1][0], editState.snapSegment[1][1]],
              ],
            },
            properties: {},
          },
        ],
      });
    } else {
      snapSegmentSource.setData(EMPTY_COLLECTION);
    }
  }

  function syncPolygonDrawSources(drawState: PolygonDrawState = polygonDrawRef.current) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    const drawSource = map.getSource(POLYGON_DRAW_PREVIEW_SOURCE_ID) as GeoJSONSource | undefined;
    if (!drawSource) {
      return;
    }

    drawSource.setData(buildPolygonDrawPreviewCollection(drawState));
  }

  function syncGeoJsonSource(data: AnyFeatureCollection) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    const geoJsonSource = map.getSource('geojson-data') as GeoJSONSource | undefined;
    geoJsonSource?.setData(withPolygonColors(data, buildPolygonColorById(data)));
  }

  function closePolygonGeometryEdit() {
    draggingVertexRef.current = null;
    mapRef.current?.dragPan.enable();
    setPolygonGeometryEdit({
      open: false,
      appFeatureId: null,
      draftFeature: null,
      draggingVertexId: null,
      snapCoordinate: null,
      snapSegment: null,
      snapKind: 'none',
    });
  }

  function closePolygonDraw() {
    setPolygonDraw({
      open: false,
      sourceFileId: null,
      sourceFileName: '',
      coordinates: [],
      cursorCoordinate: null,
    });
  }

  function startPolygonDraw(fileId: string, fileName: string) {
    closePolygonGeometryEdit();
    setEditingPolygonId(null);
    setEditingPolygonNameDraft('');
    closeContextMenu();
    closePolygonMenu();
    closeSmoothPanel();

    const map = mapRef.current;
    if (map) {
      clearSelectedFeature(map);
    }

    setPolygonDraw({
      open: true,
      sourceFileId: fileId,
      sourceFileName: fileName,
      coordinates: [],
      cursorCoordinate: null,
    });
    setError('');
    setOperationAlert(null);
  }

  function finishPolygonDraw() {
    const drawState = polygonDrawRef.current;
    if (!drawState.open || !drawState.sourceFileId) {
      return;
    }

    if (drawState.coordinates.length < 3) {
      setError('Add at least 3 vertices to finish the polygon.');
      return;
    }

    const fileId = drawState.sourceFileId;
    const fileName = drawState.sourceFileName;
    const appFeatureId = `feature-${fileId}-manual-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
    const existingFeaturesInFile = displayDataRef.current.features.filter(
      (feature) => feature.properties?.sourceFileId === fileId,
    ).length;

    const newFeature: Feature<Geometry, GeoJsonProperties> = {
      type: 'Feature',
      geometry: {
        type: 'Polygon',
        coordinates: [[...drawState.coordinates, [...drawState.coordinates[0]]]],
      },
      properties: {
        sourceFileId: fileId,
        sourceFileName: fileName,
        sourceFeatureIndex: existingFeaturesInFile,
        appFeatureId,
      },
    };

    recordHistorySnapshot();
    const newDisplayData: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: [...displayDataRef.current.features, newFeature],
    };

    setDisplayData(newDisplayData);
    setUploadedFiles((previous) =>
      previous.map((file) =>
        file.id === fileId
          ? {
              ...file,
              featureCount: file.featureCount + 1,
              polygonCount: file.polygonCount + 1,
            }
          : file,
      ),
    );

    closePolygonDraw();
    syncGeoJsonSource(newDisplayData);
    syncCsvPointSource(csvPointDataRef.current, buildPolygonBoundaryIndex(newDisplayData));
    fitMapToCollection({
      type: 'FeatureCollection',
      features: [newFeature],
    });

    const map = mapRef.current;
    if (map) {
      setSelectedFeature(map, appFeatureId);
    }

    setError('');
    setOperationAlert({
      type: 'success',
      message: `Added a new polygon to ${fileName}.`,
    });
  }

  function startPolygonGeometryEdit(appFeatureId: string) {
    const targetFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    if (!targetFeature || !isPolygonFeature(targetFeature)) {
      return;
    }

    const polygonFeature = clonePolygonFeatureGeometry(
      targetFeature as Feature<Polygon | MultiPolygon, GeoJsonProperties>,
    );

    draggingVertexRef.current = null;
    setPolygonGeometryEdit({
      open: true,
      appFeatureId,
      draftFeature: polygonFeature,
      draggingVertexId: null,
      snapCoordinate: null,
      snapSegment: null,
      snapKind: 'none',
    });
    closeSmoothPanel();
    closeContextMenu();
  }

  function startPolygonEditSession(appFeatureId: string) {
    closePolygonDraw();

    setCollapsedPolygonIds((previous) => {
      if (!previous.has(appFeatureId)) {
        return previous;
      }

      const next = new Set(previous);
      next.delete(appFeatureId);
      return next;
    });

    setEditingPolygonId(appFeatureId);
    setEditingPolygonNameDraft(polygonNameById[appFeatureId] || '');
    startPolygonGeometryEdit(appFeatureId);
  }

  async function savePolygonEditSession(appFeatureId: string) {
    if (savingPolygonEditId === appFeatureId) {
      return;
    }

    setSavingPolygonEditId(appFeatureId);
    setOperationAlert(null);
    await waitForUiPaint();

    const nextName = editingPolygonNameDraft.trim() || polygonNameById[appFeatureId] || 'Polygon';
    const geometryEditState = polygonGeometryEditRef.current;
    const hasGeometryDraft =
      geometryEditState.open &&
      geometryEditState.appFeatureId === appFeatureId &&
      geometryEditState.draftFeature;

    try {
      if (!hasGeometryDraft) {
        handlePolygonNameChange(appFeatureId, nextName);
        setEditingPolygonId(null);
        setEditingPolygonNameDraft('');
        setError('');
        setOperationAlert({
          type: 'success',
          message: 'Polygon edits saved.',
        });
        return;
      }

      const draftFeature = geometryEditState.draftFeature as Feature<Polygon | MultiPolygon, GeoJsonProperties>;

      recordHistorySnapshot();
      const newDisplayData: AnyFeatureCollection = {
        type: 'FeatureCollection',
        features: displayDataRef.current.features.map((feature) =>
          feature.properties?.appFeatureId === appFeatureId
            ? ({
                ...draftFeature,
                properties: {
                  ...feature.properties,
                  ...draftFeature.properties,
                },
              } as Feature<Geometry, GeoJsonProperties>)
            : feature,
        ),
      };

      setDisplayData(newDisplayData);
      setPolygonNames((previous) => ({
        ...previous,
        [appFeatureId]: nextName,
      }));
      syncGeoJsonSource(newDisplayData);
      syncCsvPointSource(csvPointDataRef.current, buildPolygonBoundaryIndex(newDisplayData));
      closePolygonGeometryEdit();
      setEditingPolygonId(null);
      setEditingPolygonNameDraft('');
      setError('');
      setOperationAlert({
        type: 'success',
        message: 'Polygon edits saved.',
      });
    } finally {
      setSavingPolygonEditId(null);
    }
  }

  function cancelPolygonEditSession(appFeatureId: string) {
    if (editingPolygonId === appFeatureId) {
      setEditingPolygonId(null);
      setEditingPolygonNameDraft('');
    }

    if (polygonGeometryEditRef.current.open && polygonGeometryEditRef.current.appFeatureId === appFeatureId) {
      closePolygonGeometryEdit();
    }
  }

  useEffect(() => {
    displayDataRef.current = displayData;
  }, [displayData]);

  useEffect(() => {
    csvPointDataRef.current = csvPointData;
  }, [csvPointData]);

  useEffect(() => {
    polygonGeometryEditRef.current = polygonGeometryEdit;
  }, [polygonGeometryEdit]);

  useEffect(() => {
    polygonDrawRef.current = polygonDraw;
  }, [polygonDraw]);

  useEffect(() => {
    let isCancelled = false;

    async function restorePersistedWorkspace() {
      try {
        const snapshot = await loadPersistedWorkspaceSnapshot();
        if (isCancelled || !snapshot) {
          return;
        }

        applyWorkspaceSnapshot(snapshot);
        setUndoStack([]);
        setRedoStack([]);

        const restoredFeatures = [...snapshot.displayData.features, ...snapshot.csvPointData.features];
        if (restoredFeatures.length > 0) {
          fitMapToCollection({
            type: 'FeatureCollection',
            features: restoredFeatures,
          });
        }
      } catch {
      } finally {
        if (!isCancelled) {
          hasRestoredWorkspaceRef.current = true;
          setIsRestoringWorkspace(false);
        }
      }
    }

    void restorePersistedWorkspace();

    return () => {
      isCancelled = true;
    };
  }, []);

  useEffect(() => {
    if (!hasRestoredWorkspaceRef.current) {
      return;
    }

    const snapshot = createWorkspaceSnapshot();
    if (isWorkspaceSnapshotEmpty(snapshot)) {
      void clearPersistedWorkspaceSnapshot().catch(() => undefined);
      return;
    };

    void savePersistedWorkspaceSnapshot(snapshot).catch(() => undefined);
  }, [displayData, csvPointData, csvPointFiles, uploadedFiles, polygonNames]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map || !isMapStyleReady) {
      return;
    }

    syncPolygonGeometryEditSources(polygonGeometryEdit);
  }, [isMapStyleReady, polygonGeometryEdit]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map || !isMapStyleReady) {
      return;
    }

    syncPolygonDrawSources(polygonDraw);
  }, [isMapStyleReady, polygonDraw]);

  const polygonColorById = useMemo(() => buildPolygonColorById(displayData), [displayData]);

  useEffect(() => {
    polygonColorByIdRef.current = polygonColorById;
  }, [polygonColorById]);

  useEffect(() => {
    if (!operationAlert) {
      return;
    }

    const timeoutId = window.setTimeout(() => {
      setOperationAlert(null);
    }, 4500);

    return () => {
      window.clearTimeout(timeoutId);
    };
  }, [operationAlert]);

  useEffect(() => {
    showStatesRef.current = showStates;
  }, [showStates]);

  const polygonItems = useMemo<PolygonListItem[]>(() => {
    return displayData.features.flatMap((feature, index) => {
      if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
        return [];
      }

      const appFeatureId = feature.properties?.appFeatureId;
      const sourceFileId = feature.properties?.sourceFileId;
      const sourceFileName = feature.properties?.sourceFileName;

      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return [];
      }

      const stateName =
        typeof feature.properties?.stateName === 'string' ? feature.properties.stateName : undefined;

      return [
        {
          appFeatureId,
          sourceFileId: typeof sourceFileId === 'string' ? sourceFileId : 'unknown',
          sourceFileName: typeof sourceFileName === 'string' ? sourceFileName : 'Unknown File',
          defaultName: getPolygonDefaultName(feature as Feature<Geometry, GeoJsonProperties>, index),
          isMultiPolygon: feature.geometry?.type === 'MultiPolygon',
          stateName,
          stateBadge: getStateCodeLabel(stateName),
          splitByState: Boolean(feature.properties?.splitByState),
        },
      ];
    });
  }, [displayData]);

  const polygonNameById = useMemo(() => {
    const lookup: Record<string, string> = {};
    polygonItems.forEach((item) => {
      lookup[item.appFeatureId] = polygonNames[item.appFeatureId] || item.defaultName;
    });
    return lookup;
  }, [polygonItems, polygonNames]);

  const polygonMetricsById = useMemo<Record<string, GeometryMetrics>>(() => {
    const lookup: Record<string, GeometryMetrics> = {};
    displayData.features.forEach((feature) => {
      const appFeatureId = feature.properties?.appFeatureId;
      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return;
      }

      lookup[appFeatureId] = countFeatureGeometryMetrics(feature as Feature<Geometry, GeoJsonProperties>);
    });
    return lookup;
  }, [displayData]);

  const smoothPreviewData = useMemo<AnyFeatureCollection>(() => {
    if (!smoothPanel.open || !smoothPanel.appFeatureId) {
      return displayData;
    }

    return {
      type: 'FeatureCollection',
      features: displayData.features.map((feature) => {
        if (feature.properties?.appFeatureId !== smoothPanel.appFeatureId) {
          return feature;
        }

        if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
          return feature;
        }

        return smoothPolygonFeature(feature as Parameters<typeof smoothPolygonFeature>[0], {
          algorithm: smoothPanel.algorithm,
          sensitivity: smoothPanel.sensitivity,
        });
      }),
    };
  }, [displayData, smoothPanel]);

  const smoothGeometryMetrics = useMemo<
    | {
        original: GeometryMetrics;
        preview: GeometryMetrics;
      }
    | null
  >(() => {
    if (!smoothPanel.open || !smoothPanel.appFeatureId) {
      return null;
    }

    const originalFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === smoothPanel.appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;
    const previewFeature = smoothPreviewData.features.find(
      (feature) => feature.properties?.appFeatureId === smoothPanel.appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    return {
      original: countFeatureGeometryMetrics(originalFeature),
      preview: countFeatureGeometryMetrics(previewFeature),
    };
  }, [displayData, smoothPreviewData, smoothPanel.appFeatureId, smoothPanel.open]);

  useEffect(() => {
    polygonNameByIdRef.current = polygonNameById;
  }, [polygonNameById]);

  useEffect(() => {
    if (!selectedFeatureId) {
      return;
    }

    const el = document.querySelector<HTMLElement>(`[data-appfeatureid="${CSS.escape(selectedFeatureId)}"]`);
    el?.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }, [selectedFeatureId]);

  const filesWithPolygons = useMemo(() => {
    const byFileId: Record<string, PolygonListItem[]> = {};

    polygonItems.forEach((item) => {
      if (!byFileId[item.sourceFileId]) {
        byFileId[item.sourceFileId] = [];
      }
      byFileId[item.sourceFileId].push(item);
    });

    const primaryGroups = uploadedFiles.map((file) => ({
      id: file.id,
      name: file.name,
      polygons: byFileId[file.id] || [],
      featureCount: file.featureCount,
      polygonCount: file.polygonCount,
    }));

    const knownIds = new Set(uploadedFiles.map((file) => file.id));
    const fallbackGroups = Object.entries(byFileId)
      .filter(([fileId]) => !knownIds.has(fileId))
      .map(([fileId, polygons]) => ({
        id: fileId,
        name: polygons[0]?.sourceFileName || 'Unknown File',
        polygons,
        featureCount: polygons.length,
        polygonCount: polygons.length,
      }));

    return [...primaryGroups, ...fallbackGroups];
  }, [uploadedFiles, polygonItems]);

  const polygonBoundaryIndex = useMemo(() => buildPolygonBoundaryIndex(displayData), [displayData]);

  useEffect(() => {
    setPolygonNames((previous) => {
      const next: Record<string, string> = {};

      polygonItems.forEach((item) => {
        next[item.appFeatureId] = previous[item.appFeatureId] || item.defaultName;
      });

      return next;
    });
  }, [polygonItems]);

  useEffect(() => {
    if (!editingPolygonId) {
      return;
    }

    const exists = polygonItems.some((item) => item.appFeatureId === editingPolygonId);
    if (!exists) {
      setEditingPolygonId(null);
      setEditingPolygonNameDraft('');
    }
  }, [editingPolygonId, polygonItems]);

  useEffect(() => {
    if (!polygonGeometryEdit.open || !polygonGeometryEdit.appFeatureId) {
      return;
    }

    const exists = displayData.features.some(
      (feature) => feature.properties?.appFeatureId === polygonGeometryEdit.appFeatureId,
    );
    if (!exists) {
      closePolygonGeometryEdit();
    }
  }, [displayData, polygonGeometryEdit.appFeatureId, polygonGeometryEdit.open]);

  useEffect(() => {
    setCollapsedPolygonIds((previous) => {
      const validIds = new Set(polygonItems.map((item) => item.appFeatureId));
      const next = new Set<string>();

      previous.forEach((id) => {
        if (validIds.has(id)) {
          next.add(id);
        }
      });

      return next;
    });
  }, [polygonItems]);

  function togglePolygonExpanded(appFeatureId: string) {
    setCollapsedPolygonIds((previous) => {
      const next = new Set(previous);
      if (next.has(appFeatureId)) {
        next.delete(appFeatureId);
      } else {
        next.add(appFeatureId);
      }
      return next;
    });
  }

  function clearHoveredFeature(map: Map) {
    if (!hoveredFeatureIdRef.current) {
      return;
    }

    const source = map.getSource('geojson-data');
    if (source) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: hoveredFeatureIdRef.current,
        },
        { hover: false },
      );
    }

    hoveredFeatureIdRef.current = null;
  }

  function clearSelectedFeature(map: Map) {
    if (!selectedFeatureIdRef.current) {
      return;
    }

    const source = map.getSource('geojson-data');
    if (source) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: false },
      );
    }

    selectedFeatureIdRef.current = null;
    setSelectedFeatureId(null);
  }

  function setSelectedFeature(map: Map, appFeatureId: string | null) {
    if (selectedFeatureIdRef.current && selectedFeatureIdRef.current !== appFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: false },
      );
    }

    selectedFeatureIdRef.current = appFeatureId;
    setSelectedFeatureId(appFeatureId);

    if (appFeatureId && map.getSource('geojson-data')) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: appFeatureId,
        },
        { selected: true },
      );
    }
  }

  function setHoveredFeature(map: Map, nextFeatureId: string | null) {
    if (hoveredFeatureIdRef.current && hoveredFeatureIdRef.current !== nextFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: hoveredFeatureIdRef.current,
        },
        { hover: false },
      );
    }

    if (nextFeatureId && hoveredFeatureIdRef.current !== nextFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: nextFeatureId,
        },
        { hover: true },
      );
    }

    hoveredFeatureIdRef.current = nextFeatureId;
  }

  async function refreshStateBoundarySource(map: Map) {
    const stateSource = map.getSource('state-boundaries') as GeoJSONSource | undefined;
    if (!stateSource) {
      return;
    }

    try {
      const states = await getStateBoundaries();
      stateSource.setData(states);
      setError('');
    } catch {
      setError('Could not load detailed state boundaries.');
    }
  }

  function ensureMapDataLayers(map: Map) {
    if (!map.getSource('state-boundaries')) {
      map.addSource('state-boundaries', {
        type: 'geojson',
        data: getEmptyStateBoundaries(),
      });
    }

    if (!map.getLayer('state-boundaries-line')) {
      map.addLayer({
        id: 'state-boundaries-line',
        type: 'line',
        source: 'state-boundaries',
        paint: {
          'line-color': '#0b3d91',
          'line-opacity': 0.55,
          'line-width': 1,
        },
      });
    }

    if (!map.getSource('geojson-data')) {
      map.addSource('geojson-data', {
        type: 'geojson',
        data: EMPTY_COLLECTION,
        promoteId: 'appFeatureId',
      });
    }

    if (!map.getSource('csv-point-data')) {
      map.addSource('csv-point-data', {
        type: 'geojson',
        data: EMPTY_COLLECTION,
        cluster: true,
        clusterMaxZoom: 12,
        clusterRadius: 48,
        clusterProperties: {
          insideCount: ['+', ['case', ['boolean', ['get', 'insideGeoJsonBoundary'], false], 1, 0]],
          outsideCount: ['+', ['case', ['boolean', ['get', 'insideGeoJsonBoundary'], false], 0, 1]],
        },
      });
    }

    if (!map.getSource(POLYGON_EDIT_OUTLINE_SOURCE_ID)) {
      map.addSource(POLYGON_EDIT_OUTLINE_SOURCE_ID, {
        type: 'geojson',
        data: EMPTY_COLLECTION,
      });
    }

    if (!map.getSource(POLYGON_EDIT_VERTICES_SOURCE_ID)) {
      map.addSource(POLYGON_EDIT_VERTICES_SOURCE_ID, {
        type: 'geojson',
        data: EMPTY_COLLECTION,
      });
    }

    if (!map.getSource(POLYGON_EDIT_SNAP_POINT_SOURCE_ID)) {
      map.addSource(POLYGON_EDIT_SNAP_POINT_SOURCE_ID, {
        type: 'geojson',
        data: EMPTY_COLLECTION,
      });
    }

    if (!map.getSource(POLYGON_EDIT_SNAP_SEGMENT_SOURCE_ID)) {
      map.addSource(POLYGON_EDIT_SNAP_SEGMENT_SOURCE_ID, {
        type: 'geojson',
        data: EMPTY_COLLECTION,
      });
    }

    if (!map.getSource(POLYGON_DRAW_PREVIEW_SOURCE_ID)) {
      map.addSource(POLYGON_DRAW_PREVIEW_SOURCE_ID, {
        type: 'geojson',
        data: EMPTY_COLLECTION,
      });
    }

    if (!map.getLayer('geojson-fill')) {
      map.addLayer({
        id: 'geojson-fill',
        type: 'fill',
        source: 'geojson-data',
        filter: ['in', ['geometry-type'], ['literal', ['Polygon', 'MultiPolygon']]],
        paint: {
          'fill-color': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            POLYGON_SELECTED_FILL_COLOR,
            ['boolean', ['feature-state', 'hover'], false],
            POLYGON_HOVER_FILL_COLOR,
            ['coalesce', ['get', 'polygonColor'], POLYGON_FILL_COLOR],
          ],
          'fill-opacity': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            0.72,
            ['boolean', ['feature-state', 'hover'], false],
            0.62,
            0.35,
          ],
        },
      });
    }

    if (!map.getLayer('geojson-line')) {
      map.addLayer({
        id: 'geojson-line',
        type: 'line',
        source: 'geojson-data',
        paint: {
          'line-color': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            '#7c2d12',
            ['boolean', ['feature-state', 'hover'], false],
            '#020617',
            '#111827',
          ],
          'line-width': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            4.2,
            ['boolean', ['feature-state', 'hover'], false],
            3.2,
            2,
          ],
        },
      });
    }

    if (!map.getLayer(POLYGON_EDIT_OUTLINE_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_EDIT_OUTLINE_LAYER_ID,
        type: 'line',
        source: POLYGON_EDIT_OUTLINE_SOURCE_ID,
        paint: {
          'line-color': '#f59e0b',
          'line-width': 2.5,
          'line-dasharray': [2, 2],
        },
      });
    }

    if (!map.getLayer(POLYGON_EDIT_VERTICES_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_EDIT_VERTICES_LAYER_ID,
        type: 'circle',
        source: POLYGON_EDIT_VERTICES_SOURCE_ID,
        paint: {
          'circle-radius': 4.5,
          'circle-color': '#f97316',
          'circle-stroke-width': 2,
          'circle-stroke-color': '#ffffff',
        },
      });
    }

    if (!map.getLayer(POLYGON_EDIT_SNAP_SEGMENT_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_EDIT_SNAP_SEGMENT_LAYER_ID,
        type: 'line',
        source: POLYGON_EDIT_SNAP_SEGMENT_SOURCE_ID,
        paint: {
          'line-color': '#06b6d4',
          'line-width': 3,
          'line-opacity': 0.8,
          'line-dasharray': [1, 1],
        },
      });
    }

    if (!map.getLayer(POLYGON_EDIT_SNAP_POINT_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_EDIT_SNAP_POINT_LAYER_ID,
        type: 'circle',
        source: POLYGON_EDIT_SNAP_POINT_SOURCE_ID,
        paint: {
          'circle-radius': 6,
          'circle-color': [
            'case',
            ['==', ['get', 'kind'], 'vertex'],
            '#2563eb',
            '#06b6d4',
          ],
          'circle-stroke-width': 2,
          'circle-stroke-color': '#ffffff',
        },
      });
    }

    if (!map.getLayer(POLYGON_DRAW_FILL_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_DRAW_FILL_LAYER_ID,
        type: 'fill',
        source: POLYGON_DRAW_PREVIEW_SOURCE_ID,
        filter: ['==', ['geometry-type'], 'Polygon'],
        paint: {
          'fill-color': '#2563eb',
          'fill-opacity': 0.2,
        },
      });
    }

    if (!map.getLayer(POLYGON_DRAW_LINE_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_DRAW_LINE_LAYER_ID,
        type: 'line',
        source: POLYGON_DRAW_PREVIEW_SOURCE_ID,
        filter: ['==', ['geometry-type'], 'LineString'],
        paint: {
          'line-color': '#2563eb',
          'line-width': 2.5,
          'line-dasharray': [2, 1],
        },
      });
    }

    if (!map.getLayer(POLYGON_DRAW_VERTICES_LAYER_ID)) {
      map.addLayer({
        id: POLYGON_DRAW_VERTICES_LAYER_ID,
        type: 'circle',
        source: POLYGON_DRAW_PREVIEW_SOURCE_ID,
        filter: ['==', ['geometry-type'], 'Point'],
        paint: {
          'circle-radius': 4,
          'circle-color': '#2563eb',
          'circle-stroke-width': 2,
          'circle-stroke-color': '#ffffff',
        },
      });
    }

    if (!map.getLayer('geojson-point')) {
      map.addLayer({
        id: 'geojson-point',
        type: 'circle',
        source: 'geojson-data',
        filter: ['==', ['geometry-type'], 'Point'],
        paint: {
          'circle-radius': 5,
          'circle-color': '#111827',
          'circle-stroke-color': '#fff7ed',
          'circle-stroke-width': 2,
        },
      });
    }

    if (!map.getLayer('csv-point-clusters')) {
      map.addLayer({
        id: 'csv-point-clusters',
        type: 'circle',
        source: 'csv-point-data',
        filter: ['has', 'point_count'],
        paint: {
          'circle-color': [
            'case',
            ['==', ['get', 'outsideCount'], 0],
            CSV_INSIDE_COLOR,
            ['==', ['get', 'insideCount'], 0],
            CSV_OUTSIDE_COLOR,
            CSV_MIXED_CLUSTER_COLOR,
          ],
          'circle-radius': [
            'step',
            ['get', 'point_count'],
            14,
            100,
            18,
            1000,
            24,
          ],
          'circle-stroke-color': '#ffffff',
          'circle-stroke-width': 1.5,
          'circle-opacity': 0.9,
        },
      });
    }

    if (!map.getLayer('csv-point-cluster-count')) {
      map.addLayer({
        id: 'csv-point-cluster-count',
        type: 'symbol',
        source: 'csv-point-data',
        filter: ['has', 'point_count'],
        layout: {
          'text-field': '{point_count_abbreviated}',
          'text-font': ['Open Sans Bold'],
          'text-size': 11,
        },
        paint: {
          'text-color': '#ffffff',
        },
      });
    }

    if (!map.getLayer('csv-point-unclustered')) {
      map.addLayer({
        id: 'csv-point-unclustered',
        type: 'circle',
        source: 'csv-point-data',
        filter: ['!', ['has', 'point_count']],
        paint: {
          'circle-radius': 3.5,
          'circle-color': ['case', ['boolean', ['get', 'insideGeoJsonBoundary'], false], CSV_INSIDE_COLOR, CSV_OUTSIDE_COLOR],
          'circle-stroke-color': '#ffffff',
          'circle-stroke-width': 1,
          'circle-opacity': 0.85,
        },
      });
    }

    void refreshStateBoundarySource(map);

    const dataSource = map.getSource('geojson-data') as GeoJSONSource | undefined;
    dataSource?.setData(withPolygonColors(displayDataRef.current, polygonColorByIdRef.current));
    const csvPointSource = map.getSource('csv-point-data') as GeoJSONSource | undefined;
    csvPointSource?.setData(getClassifiedCsvPointData(csvPointDataRef.current, buildPolygonBoundaryIndex(displayDataRef.current)));
    syncPolygonGeometryEditSources();
    syncPolygonDrawSources();
    clearHoveredFeature(map);

    if (selectedFeatureIdRef.current) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: true },
      );
    }

    map.setLayoutProperty('state-boundaries-line', 'visibility', showStatesRef.current ? 'visible' : 'none');
  }

  useEffect(() => {
    if (!mapContainerRef.current || mapRef.current) {
      return;
    }

    const map = new maplibregl.Map({
      container: mapContainerRef.current,
      style: BASEMAP_STYLE,
      center: [-96, 38],
      zoom: 3,
    });

    map.addControl(new maplibregl.NavigationControl(), 'top-right');

    map.on('style.load', () => {
      setIsMapStyleReady(true);
      ensureMapDataLayers(map);

      if (pendingFitBoundsRef.current) {
        fitMapToBounds(pendingFitBoundsRef.current);
      }
    });

    map.on('click', 'csv-point-clusters', (event) => {
      const clusterFeature = event.features?.[0];
      if (!clusterFeature || clusterFeature.geometry?.type !== 'Point') {
        return;
      }

      const clusterIdValue = clusterFeature.properties?.cluster_id;
      const clusterId = typeof clusterIdValue === 'number' ? clusterIdValue : Number(clusterIdValue);
      if (!Number.isFinite(clusterId)) {
        return;
      }

      const coordinates = clusterFeature.geometry.coordinates;

      const source = map.getSource('csv-point-data') as GeoJSONSource | undefined;
      if (!source) {
        return;
      }

      void source.getClusterExpansionZoom(clusterId).then((zoom) => {
        map.easeTo({
          center: [coordinates[0], coordinates[1]],
          zoom,
          duration: 400,
        });
      });
    });

    map.on('mouseenter', 'csv-point-clusters', () => {
      map.getCanvas().style.cursor = 'pointer';
    });

    map.on('mouseleave', 'csv-point-clusters', () => {
      map.getCanvas().style.cursor = '';
    });

    map.on('mouseenter', 'csv-point-unclustered', () => {
      map.getCanvas().style.cursor = 'pointer';
    });

    map.on('mouseleave', 'csv-point-unclustered', () => {
      map.getCanvas().style.cursor = '';
    });

    const finishVertexDrag = () => {
      draggingVertexRef.current = null;
      map.dragPan.enable();
      setPolygonGeometryEdit((previous) => ({
        ...previous,
        draggingVertexId: null,
        snapCoordinate: null,
        snapSegment: null,
        snapKind: 'none',
      }));
    };

    map.on('mousedown', (event) => {
      if (polygonDrawRef.current.open) {
        return;
      }

      if (!polygonGeometryEditRef.current.open || !polygonGeometryEditRef.current.draftFeature) {
        return;
      }

      const mouseEvent = event.originalEvent as MouseEvent;
      const isRightClickDeleteIntent = mouseEvent.button === 2 || (mouseEvent.button === 0 && mouseEvent.ctrlKey);
      const isPrimaryClick = mouseEvent.button === 0 && !mouseEvent.ctrlKey;

      if (!isPrimaryClick && !isRightClickDeleteIntent) {
        return;
      }

      const nearestVertex = findNearestVertexForCoordinate(
        map,
        polygonGeometryEditRef.current.draftFeature,
        [event.lngLat.lng, event.lngLat.lat],
        16,
      );
      if (!nearestVertex) {
        return;
      }

      const nextReference = nearestVertex.reference;

      event.preventDefault();
      event.originalEvent.stopPropagation();
      suppressNextMapClickRef.current = true;

      if (isRightClickDeleteIntent) {
        setPolygonGeometryEdit((previous) => {
          if (!previous.draftFeature) {
            return previous;
          }

          return {
            ...previous,
            draftFeature: removePolygonVertex(previous.draftFeature, nextReference),
            draggingVertexId: null,
            snapCoordinate: null,
            snapSegment: null,
            snapKind: 'none',
          };
        });
        return;
      }

      if (mouseEvent.shiftKey) {
        setPolygonGeometryEdit((previous) => {
          if (!previous.draftFeature) {
            return previous;
          }

          return {
            ...previous,
            draftFeature: removePolygonVertex(previous.draftFeature, nextReference),
            draggingVertexId: null,
            snapCoordinate: null,
            snapSegment: null,
            snapKind: 'none',
          };
        });
        return;
      }

      draggingVertexRef.current = nextReference;
      map.dragPan.disable();

      setPolygonGeometryEdit((previous) => ({
        ...previous,
        draggingVertexId: nearestVertex.vertexId,
      }));
    });

    map.on('click', (event) => {
      if (draggingVertexRef.current) {
        return;
      }

      if (suppressNextMapClickRef.current) {
        suppressNextMapClickRef.current = false;
        return;
      }

      if (polygonDrawRef.current.open) {
        event.preventDefault();
        event.originalEvent.stopPropagation();

        const nextCoordinate: [number, number] = [event.lngLat.lng, event.lngLat.lat];
        setPolygonDraw((previous) => {
          if (!previous.open) {
            return previous;
          }

          return {
            ...previous,
            coordinates: [...previous.coordinates, nextCoordinate],
            cursorCoordinate: nextCoordinate,
          };
        });
        setError('');
        return;
      }

      if (polygonGeometryEditRef.current.open && polygonGeometryEditRef.current.draftFeature) {
        const nearestVertex = findNearestVertexForCoordinate(
          map,
          polygonGeometryEditRef.current.draftFeature,
          [event.lngLat.lng, event.lngLat.lat],
          14,
        );
        if (nearestVertex) {
          return;
        }

        const nearestSegment = findNearestSegmentForCoordinate(
          map,
          polygonGeometryEditRef.current.draftFeature,
          [event.lngLat.lng, event.lngLat.lat],
          POLYGON_EDIT_SNAP_THRESHOLD_PX + 10,
        );
        if (!nearestSegment) {
          return;
        }

        event.preventDefault();
        event.originalEvent.stopPropagation();

        setPolygonGeometryEdit((previous) => {
          if (!previous.draftFeature) {
            return previous;
          }

          return {
            ...previous,
            draftFeature: insertPolygonVertexOnSegment(
              previous.draftFeature,
              nearestSegment.reference,
              nearestSegment.snappedCoordinate,
            ),
            snapCoordinate: nearestSegment.snappedCoordinate,
            snapSegment: null,
            snapKind: 'vertex',
          };
        });

        return;
      }

      if (polygonGeometryEditRef.current.open) {
        return;
      }

      if (!map.getLayer('geojson-fill')) {
        closeContextMenu();
        return;
      }

      const hits = map.queryRenderedFeatures(event.point, { layers: ['geojson-fill'] });
      const appFeatureId = hits[0]?.properties?.appFeatureId;

      if (!appFeatureId || typeof appFeatureId !== 'string') {
        closeContextMenu();
        return;
      }

      const currentName = polygonNameByIdRef.current[appFeatureId] || 'Polygon';

      if (selectedFeatureIdRef.current === appFeatureId) {
        clearSelectedFeature(map);
        closeContextMenu();
        closePolygonMenu();
        return;
      }

      setContextMenu({
        open: true,
        x: event.point.x,
        y: event.point.y,
        appFeatureId,
        nameDraft: currentName,
      });
      setSelectedFeature(map, appFeatureId);
      closePolygonMenu();
    });

    map.on('mouseenter', POLYGON_EDIT_OUTLINE_LAYER_ID, () => {
      if (!draggingVertexRef.current && polygonGeometryEditRef.current.open) {
        map.getCanvas().style.cursor = 'copy';
      }
    });

    map.on('mouseleave', POLYGON_EDIT_OUTLINE_LAYER_ID, () => {
      if (!draggingVertexRef.current) {
        map.getCanvas().style.cursor = '';
      }
    });

    map.on('mouseenter', POLYGON_EDIT_VERTICES_LAYER_ID, () => {
      map.getCanvas().style.cursor = draggingVertexRef.current ? 'grabbing' : 'grab';
    });

    map.on('mouseleave', POLYGON_EDIT_VERTICES_LAYER_ID, () => {
      if (!draggingVertexRef.current) {
        map.getCanvas().style.cursor = '';
      }
    });

    map.on('mouseup', () => {
      if (draggingVertexRef.current) {
        finishVertexDrag();
      }
    });

    map.on('mousemove', (event) => {
      if (polygonDrawRef.current.open) {
        const nextCoordinate: [number, number] = [event.lngLat.lng, event.lngLat.lat];
        setPolygonDraw((previous) => {
          if (!previous.open) {
            return previous;
          }

          if (
            previous.cursorCoordinate &&
            previous.cursorCoordinate[0] === nextCoordinate[0] &&
            previous.cursorCoordinate[1] === nextCoordinate[1]
          ) {
            return previous;
          }

          return {
            ...previous,
            cursorCoordinate: nextCoordinate,
          };
        });
        map.getCanvas().style.cursor = 'crosshair';
        return;
      }

      if (draggingVertexRef.current && polygonGeometryEditRef.current.draftFeature) {
        const activeDragReference = draggingVertexRef.current;
        const isSnapSuppressed = (event.originalEvent as MouseEvent).altKey;
        const snapResult = isSnapSuppressed
          ? {
              coordinate: [event.lngLat.lng, event.lngLat.lat] as [number, number],
              kind: 'none' as const,
              segment: undefined,
            }
          : snapCoordinateToNearbyGeometry(
              map,
              polygonGeometryEditRef.current.draftFeature,
              [event.lngLat.lng, event.lngLat.lat],
              activeDragReference,
            );

        setPolygonGeometryEdit((previous) => {
          if (!previous.draftFeature) {
            return previous;
          }

          if (!activeDragReference) {
            return previous;
          }

          return {
            ...previous,
            draftFeature: updatePolygonVertexCoordinate(previous.draftFeature, activeDragReference, snapResult.coordinate),
            snapCoordinate: snapResult.kind === 'none' ? null : snapResult.coordinate,
            snapSegment: snapResult.segment ?? null,
            snapKind: snapResult.kind,
          };
        });

        map.getCanvas().style.cursor = 'grabbing';
        return;
      }

      if (polygonGeometryEditRef.current.open && polygonGeometryEditRef.current.draftFeature) {
        const nearestVertex = findNearestVertexForCoordinate(
          map,
          polygonGeometryEditRef.current.draftFeature,
          [event.lngLat.lng, event.lngLat.lat],
          14,
        );

        if (nearestVertex) {
          setPolygonGeometryEdit((previous) => {
            if (
              previous.snapCoordinate === null &&
              previous.snapSegment === null &&
              previous.snapKind === 'none'
            ) {
              return previous;
            }

            return {
              ...previous,
              snapCoordinate: null,
              snapSegment: null,
              snapKind: 'none',
            };
          });
          map.getCanvas().style.cursor = 'grab';
          return;
        }

        const nearestSegment = findNearestSegmentForCoordinate(
          map,
          polygonGeometryEditRef.current.draftFeature,
          [event.lngLat.lng, event.lngLat.lat],
          POLYGON_EDIT_SNAP_THRESHOLD_PX + 10,
        );

        if (!nearestSegment) {
          setPolygonGeometryEdit((previous) => {
            if (
              previous.snapCoordinate === null &&
              previous.snapSegment === null &&
              previous.snapKind === 'none'
            ) {
              return previous;
            }

            return {
              ...previous,
              snapCoordinate: null,
              snapSegment: null,
              snapKind: 'none',
            };
          });
          map.getCanvas().style.cursor = '';
          return;
        }

        setPolygonGeometryEdit((previous) => {
          if (!previous.draftFeature) {
            return previous;
          }

          const previewSegment = getSegmentCoordinates(previous.draftFeature, nearestSegment.reference);

          const hadSameCoordinate =
            previous.snapCoordinate !== null &&
            previous.snapCoordinate[0] === nearestSegment.snappedCoordinate[0] &&
            previous.snapCoordinate[1] === nearestSegment.snappedCoordinate[1];

          const hadSameSegment =
            previewSegment !== null &&
            previous.snapSegment !== null &&
            previous.snapSegment[0][0] === previewSegment[0][0] &&
            previous.snapSegment[0][1] === previewSegment[0][1] &&
            previous.snapSegment[1][0] === previewSegment[1][0] &&
            previous.snapSegment[1][1] === previewSegment[1][1];

          if (hadSameCoordinate && hadSameSegment && previous.snapKind === 'edge') {
            return previous;
          }

          return {
            ...previous,
            snapCoordinate: nearestSegment.snappedCoordinate,
            snapSegment: previewSegment,
            snapKind: 'edge',
          };
        });

        map.getCanvas().style.cursor = 'copy';
        return;
      }

      if (!map.getLayer('geojson-fill')) {
        map.getCanvas().style.cursor = '';
        return;
      }

      const hits = map.queryRenderedFeatures(event.point, { layers: ['geojson-fill'] });
      const nextId = hits[0]?.properties?.appFeatureId;
      const nextFeatureId = typeof nextId === 'string' ? nextId : null;

      setHoveredFeature(map, nextFeatureId);
      map.getCanvas().style.cursor = nextFeatureId ? 'pointer' : '';
    });

    map.on('mouseleave', () => {
      clearHoveredFeature(map);
      if (polygonDrawRef.current.open) {
        setPolygonDraw((previous) => {
          if (!previous.open || previous.cursorCoordinate === null) {
            return previous;
          }

          return {
            ...previous,
            cursorCoordinate: null,
          };
        });
      }
      map.getCanvas().style.cursor = '';
    });

    mapRef.current = map;

    return () => {
      finishVertexDrag();
      setIsMapStyleReady(false);
      clearHoveredFeature(map);
      clearSelectedFeature(map);
      map.remove();
      mapRef.current = null;
    };
  }, []);

  useEffect(() => {
    const map = mapRef.current;
    if (!map || !isMapStyleReady) {
      return;
    }

    const source = map.getSource('geojson-data') as GeoJSONSource | undefined;
    source?.setData(withPolygonColors(smoothPreviewData, polygonColorByIdRef.current));
    clearHoveredFeature(map);
  }, [isMapStyleReady, smoothPreviewData]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map || !isMapStyleReady) {
      return;
    }

    const source = map.getSource('csv-point-data') as GeoJSONSource | undefined;
    source?.setData(getClassifiedCsvPointData(csvPointData, polygonBoundaryIndex));
  }, [csvPointData, isMapStyleReady, polygonBoundaryIndex]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded()) {
      return;
    }

    closeContextMenu();
    closePolygonMenu();
  }, [displayData]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded() || !map.getLayer('state-boundaries-line')) {
      return;
    }

    map.setLayoutProperty('state-boundaries-line', 'visibility', showStates ? 'visible' : 'none');
  }, [showStates]);

  useEffect(() => {
    function handleKeyDown(event: KeyboardEvent) {
      if (!event.metaKey || shouldIgnoreHistoryShortcut(event.target)) {
        return;
      }

      const key = event.key.toLowerCase();
      if (key !== 'z') {
        return;
      }

      event.preventDefault();

      if (event.shiftKey) {
        handleRedo();
        return;
      }

      handleUndo();
    }

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [undoStack, redoStack, displayData, csvPointData, csvPointFiles, uploadedFiles, polygonNames]);

  async function importGeoJsonFiles(selectedFiles: File[]) {
    if (!selectedFiles.length) {
      return;
    }

    const importedFeatures: Feature<Geometry, GeoJsonProperties>[] = [];
    const importedFiles: UploadedFileMeta[] = [];
    const failedFiles: string[] = [];

    for (const selectedFile of selectedFiles) {
      try {
        const text = await selectedFile.text();
        const parsed = parseGeoJson(text);
        const fileId = `file-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
        const annotated = annotateImportedCollection(parsed, fileId, selectedFile.name);
        const polygonCount = annotated.features.filter((feature) => isPolygonFeature(feature)).length;

        importedFeatures.push(...annotated.features);
        importedFiles.push({
          id: fileId,
          name: selectedFile.name,
          featureCount: annotated.features.length,
          polygonCount,
        });
      } catch {
        failedFiles.push(selectedFile.name);
      }
    }

    if (importedFeatures.length > 0) {
      recordHistorySnapshot();
      const newDisplayData: AnyFeatureCollection = {
        type: 'FeatureCollection',
        features: [...displayDataRef.current.features, ...importedFeatures],
      };
      setDisplayData(newDisplayData);
      setUploadedFiles((previous) => [...previous, ...importedFiles]);

      fitMapToCollection({
        type: 'FeatureCollection',
        features: importedFeatures,
      });

      syncGeoJsonSource(newDisplayData);

      syncCsvPointSource(csvPointDataRef.current, buildPolygonBoundaryIndex(newDisplayData));
    }

    if (failedFiles.length > 0) {
      setError(`Could not parse: ${failedFiles.join(', ')}`);
    } else {
      setError('');
    }

    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }
  }

  async function handleFileChange(event: React.ChangeEvent<HTMLInputElement>) {
    const selectedFiles = Array.from(event.target.files || []);
    await handleMixedFileImport(selectedFiles);
  }

  async function handleMixedFileImport(selectedFiles: File[]) {
    if (!selectedFiles.length || isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    const geoJsonFiles: File[] = [];
    const csvFiles: File[] = [];
    const unsupportedFiles: string[] = [];

    selectedFiles.forEach((selectedFile) => {
      const normalizedName = selectedFile.name.trim().toLowerCase();

      if (normalizedName.endsWith('.csv')) {
        csvFiles.push(selectedFile);
        return;
      }

      if (normalizedName.endsWith('.geojson') || normalizedName.endsWith('.json')) {
        geoJsonFiles.push(selectedFile);
        return;
      }

      unsupportedFiles.push(selectedFile.name);
    });

    setIsHandlingUploads(true);
    setOperationAlert(null);
    setUploadStatusMessage(
      `Preparing ${selectedFiles.length} file${selectedFiles.length === 1 ? '' : 's'} for import...`,
    );
    await waitForUiPaint();

    try {
      if (geoJsonFiles.length > 0) {
        setUploadStatusMessage(
          `Processing ${geoJsonFiles.length} GeoJSON file${geoJsonFiles.length === 1 ? '' : 's'}...`,
        );
        await waitForUiPaint();
        await importGeoJsonFiles(geoJsonFiles);
      }

      if (csvFiles.length > 0) {
        setUploadStatusMessage(`Processing ${csvFiles.length} CSV file${csvFiles.length === 1 ? '' : 's'}...`);
        await waitForUiPaint();
        await importCsvPointFiles(csvFiles);
      }

      if (unsupportedFiles.length > 0) {
        const unsupportedMessage = `Unsupported file type${unsupportedFiles.length === 1 ? '' : 's'}: ${unsupportedFiles.join(', ')}`;

        if (geoJsonFiles.length > 0 || csvFiles.length > 0) {
          setError('');
          setOperationAlert({
            type: 'error',
            message: unsupportedMessage,
          });
        } else {
          setError(unsupportedMessage);
        }
      }
    } finally {
      setIsHandlingUploads(false);
      setUploadStatusMessage('');

      if (fileInputRef.current) {
        fileInputRef.current.value = '';
      }
    }
  }

  async function importCsvPointFiles(selectedFiles: File[]) {
    if (!selectedFiles.length) {
      return;
    }

    const importedPointFeatures: Feature<Geometry, GeoJsonProperties>[] = [];
    const importedCsvFiles: CsvPointFileMeta[] = [];
    const failedFiles: string[] = [];
    let importedPointCount = 0;
    let skippedPointCount = 0;

    for (const selectedFile of selectedFiles) {
      try {
        const text = await selectedFile.text();
        const csvFileId = `csv-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
        const parsed = parseCsvPointCollection(text, selectedFile.name, csvFileId);
        importedPointFeatures.push(...parsed.data.features);
        importedCsvFiles.push({
          id: csvFileId,
          name: selectedFile.name,
          pointCount: parsed.importedCount,
        });
        importedPointCount += parsed.importedCount;
        skippedPointCount += parsed.skippedCount;
      } catch {
        failedFiles.push(selectedFile.name);
      }
    }

    if (importedPointFeatures.length > 0) {
      recordHistorySnapshot();
      const newCsvPointData: AnyFeatureCollection = {
        type: 'FeatureCollection',
        features: [...csvPointDataRef.current.features, ...importedPointFeatures],
      };
      setCsvPointData(newCsvPointData);
      setCsvPointFiles((previous) => [...previous, ...importedCsvFiles]);
      syncCsvPointSource(newCsvPointData);

      fitMapToCollection({
        type: 'FeatureCollection',
        features: importedPointFeatures,
      });

      setError('');
      setOperationAlert({
        type: 'success',
        message:
          skippedPointCount > 0
            ? `Imported ${importedPointCount} coordinate points from ${importedCsvFiles.length} CSV file${
                importedCsvFiles.length === 1 ? '' : 's'
              }. Skipped ${skippedPointCount} invalid row${skippedPointCount === 1 ? '' : 's'}.`
            : `Imported ${importedPointCount} coordinate points from ${importedCsvFiles.length} CSV file${
                importedCsvFiles.length === 1 ? '' : 's'
              }.`,
      });
    }

    if (failedFiles.length > 0) {
      const failureMessage = `Could not parse CSV file${failedFiles.length === 1 ? '' : 's'}: ${failedFiles.join(', ')}`;
      if (importedPointFeatures.length > 0) {
        setError('');
        setOperationAlert({
          type: 'error',
          message: failureMessage,
        });
      } else {
        setError(failureMessage);
      }
    }

  }

  function handleUploadDropZoneClick() {
    if (isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    fileInputRef.current?.click();
  }

  function handleRemoveCsvPointFile(csvFileId: string) {
    recordHistorySnapshot();

    const newCsvPointData: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: csvPointDataRef.current.features.filter(
        (feature) => feature.properties?.csvSourceFileId !== csvFileId,
      ),
    };
    setCsvPointData(newCsvPointData);
    setCsvPointFiles((previous) => previous.filter((file) => file.id !== csvFileId));
    syncCsvPointSource(newCsvPointData);
  }

  function handleUploadDragEnter(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();

    if (isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    uploadDragDepthRef.current += 1;
    setIsDragOverUpload(true);
  }

  function handleUploadDragOver(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();

    if (isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    if (!isDragOverUpload) {
      setIsDragOverUpload(true);
    }
  }

  function handleUploadDragLeave(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();

    if (isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    uploadDragDepthRef.current = Math.max(0, uploadDragDepthRef.current - 1);
    if (uploadDragDepthRef.current === 0) {
      setIsDragOverUpload(false);
    }
  }

  async function handleUploadDrop(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();

    if (isHandlingUploads || isRestoringWorkspace) {
      return;
    }

    uploadDragDepthRef.current = 0;
    setIsDragOverUpload(false);

    const droppedFiles = Array.from(event.dataTransfer.files || []);
    await handleMixedFileImport(droppedFiles);
  }

  function handleRemoveFile(fileId: string) {
    const wasEditingRemovedFile =
      polygonGeometryEditRef.current.open &&
      displayDataRef.current.features.some(
        (feature) =>
          feature.properties?.appFeatureId === polygonGeometryEditRef.current.appFeatureId &&
          feature.properties?.sourceFileId === fileId,
      );

    const removedIds = new Set(
      displayData.features
        .filter((feature) => feature.properties?.sourceFileId === fileId)
        .map((feature) => String(feature.properties?.appFeatureId || '')),
    );

    recordHistorySnapshot();
    const newDisplayData: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: displayDataRef.current.features.filter((feature) => feature.properties?.sourceFileId !== fileId),
    };
    setDisplayData(newDisplayData);
    setUploadedFiles((previous) => previous.filter((file) => file.id !== fileId));
    syncGeoJsonSource(newDisplayData);
    syncCsvPointSource(csvPointDataRef.current, buildPolygonBoundaryIndex(newDisplayData));
    closePolygonMenu();

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current && removedIds.has(selectedFeatureIdRef.current)) {
      clearSelectedFeature(map);
    }

    if (wasEditingRemovedFile) {
      closePolygonGeometryEdit();
    }

    if (polygonDrawRef.current.open && polygonDrawRef.current.sourceFileId === fileId) {
      closePolygonDraw();
    }

    closeContextMenu();
  }

  function handleAddPolygonToFile(fileId: string, fileName: string) {
    startPolygonDraw(fileId, fileName);
  }

  function handleClearAll() {
    recordHistorySnapshot();
    setUploadedFiles([]);
    setDisplayData(EMPTY_COLLECTION);
    setCsvPointData(EMPTY_COLLECTION);
    setCsvPointFiles([]);
    syncGeoJsonSource(EMPTY_COLLECTION);
    syncCsvPointSource(EMPTY_COLLECTION, []);
    setError('');
    setPolygonNames({});
    setMergeMode(false);
    setSelectedForMerge(new Set());
    closePolygonMenu();

    const map = mapRef.current;
    if (map) {
      clearSelectedFeature(map);
    }

    closeContextMenu();
    closePolygonGeometryEdit();
    closePolygonDraw();

    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }

    void clearPersistedWorkspaceSnapshot().catch(() => undefined);

    setIsDragOverUpload(false);
    setIsHandlingUploads(false);
    setUploadStatusMessage('');
    uploadDragDepthRef.current = 0;
  }

  function toggleMergeMode() {
    setMergeMode((previous) => !previous);
    setSelectedForMerge(new Set());
    closePolygonMenu();
    closeSmoothPanel();
  }

  function toggleSelectForMerge(appFeatureId: string) {
    setSelectedForMerge((previous) => {
      const next = new Set(previous);
      if (next.has(appFeatureId)) {
        next.delete(appFeatureId);
      } else {
        next.add(appFeatureId);
      }
      return next;
    });
  }

  function handleMergeSelected() {
    if (selectedForMerge.size < 2) {
      return;
    }

    const featuresToMerge = displayData.features.filter(
      (feature) =>
        typeof feature.properties?.appFeatureId === 'string' &&
        selectedForMerge.has(feature.properties.appFeatureId) &&
        isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>),
    ) as Feature<Geometry, GeoJsonProperties>[];

    if (featuresToMerge.length < 2) {
      return;
    }

    const merged = mergePolygons(featuresToMerge as Parameters<typeof mergePolygons>[0]);
    if (!merged) {
      setError('Merge failed. Could not combine the selected polygons.');
      return;
    }

    const mergedIds = new Set(featuresToMerge.map((f) => f.properties?.appFeatureId as string));
    const firstSourceFileId = featuresToMerge[0]?.properties?.sourceFileId;
    const firstSourceFileName = featuresToMerge[0]?.properties?.sourceFileName;
    const newId = `merged-${Date.now()}`;
    const mergedNames = featuresToMerge
      .map((f) => polygonNameById[f.properties?.appFeatureId as string] || f.properties?.appFeatureId)
      .join(' + ');

    const stateNames = [
      ...new Set(
        featuresToMerge
          .map((f) => f.properties?.stateName)
          .filter((n): n is string => typeof n === 'string' && n.trim() !== ''),
      ),
    ];
    const anyWasSplit = featuresToMerge.some((f) => f.properties?.splitByState === true);

    const mergedFeature: Feature<Geometry, GeoJsonProperties> = {
      ...merged,
      properties: {
        ...merged.properties,
        appFeatureId: newId,
        sourceFileId: firstSourceFileId ?? 'merged',
        sourceFileName: firstSourceFileName ?? 'Merged',
        polygonName: mergedNames,
        splitByState: anyWasSplit,
        stateName: stateNames.length > 0 ? stateNames.join(', ') : undefined,
      },
    };

    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: [
        ...previous.features.filter(
          (feature) => !mergedIds.has(feature.properties?.appFeatureId as string),
        ),
        mergedFeature,
      ],
    }));

    setPolygonNames((previous) => ({
      ...previous,
      [newId]: mergedNames,
    }));

    setSelectedForMerge(new Set());
    setMergeMode(false);
    closeSmoothPanel();
    setError('');
  }

  async function handleSplitAll() {
    if (!displayData.features.length || isSplittingAll) {
      return;
    }

    setIsSplittingAll(true);
    setOperationAlert(null);
    await waitForUiPaint();

    try {
      const result = await splitPolygonsByStates(displayData);
      recordHistorySnapshot();
      setDisplayData(withFeatureIds(result.data, 'split-all'));
      setError('');
      const noIntersectionMessage =
        result.summary.noIntersectionCount > 0
          ? ` ${result.summary.noIntersectionCount} polygon${
              result.summary.noIntersectionCount === 1 ? '' : 's'
            } had no intersecting state boundaries.`
          : '';
      setOperationAlert({
        type: 'success',
        message:
          result.summary.splitCount > 0
            ? `Split complete. Created ${result.summary.splitCount} state pieces.${noIntersectionMessage}`
            : `Split complete. No state-boundary splits were needed.${noIntersectionMessage}`,
      });
    } catch {
      setError('Split failed. Could not split polygons by state.');
      setOperationAlert({
        type: 'error',
        message: 'Split failed. Could not split polygons by state.',
      });
    } finally {
      setIsSplittingAll(false);
    }
  }

  function handleSmoothAll() {
    if (!polygonItems.length) {
      return;
    }

    const smoothed = smoothPolygonsInCollection(displayData, {
      algorithm: 'simplify',
      sensitivity: 40,
    });
    recordHistorySnapshot();
    setDisplayData(smoothed);
    setError('');
  }

  function openSmoothPanelForFeature(appFeatureId: string, anchorElement?: HTMLElement) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target || !isPolygonFeature(target as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const rect = anchorElement?.getBoundingClientRect();
    const viewportWidth = window.innerWidth;
    const viewportHeight = window.innerHeight;

    const preferredX = rect ? rect.right - SMOOTH_PANEL_WIDTH_PX : 24;
    const minX = SMOOTH_PANEL_VIEWPORT_MARGIN_PX;
    const maxX = Math.max(minX, viewportWidth - SMOOTH_PANEL_WIDTH_PX - SMOOTH_PANEL_VIEWPORT_MARGIN_PX);
    const x = Math.max(minX, Math.min(preferredX, maxX));

    const preferredY = rect ? rect.bottom + 8 : 28;
    const maxYBelow = viewportHeight - SMOOTH_PANEL_ESTIMATED_HEIGHT_PX - SMOOTH_PANEL_VIEWPORT_MARGIN_PX;
    const fallbackAbove = rect ? rect.top - SMOOTH_PANEL_ESTIMATED_HEIGHT_PX - 8 : SMOOTH_PANEL_VIEWPORT_MARGIN_PX;
    const preferredYWithFlip = preferredY <= maxYBelow ? preferredY : fallbackAbove;
    const minY = SMOOTH_PANEL_VIEWPORT_MARGIN_PX;
    const maxY = Math.max(minY, viewportHeight - SMOOTH_PANEL_VIEWPORT_MARGIN_PX - 140);
    const y = Math.max(minY, Math.min(preferredYWithFlip, maxY));

    setSmoothPanel({
      open: true,
      appFeatureId,
      algorithm: 'simplify',
      sensitivity: 40,
      x,
      y,
    });
  }

  function applySmoothToFeature() {
    if (!smoothPanel.appFeatureId) {
      return;
    }

    recordHistorySnapshot();
    setDisplayData(smoothPreviewData);

    setError('');
    closeSmoothPanel();
  }

  async function handleSplitFeatureById(appFeatureId: string) {
    if (splittingFeatureIds.has(appFeatureId)) {
      return;
    }

    const targetFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    if (!targetFeature || !isPolygonFeature(targetFeature)) {
      return;
    }

    setSplittingFeatureIds((previous) => {
      const next = new Set(previous);
      next.add(appFeatureId);
      return next;
    });
    setOperationAlert(null);
    await waitForUiPaint();

    try {
      const splitResult = await splitPolygonsByStates({
        type: 'FeatureCollection',
        features: [targetFeature],
      });

      if (splitResult.summary.noIntersectionCount > 0) {
        setError('');
        setOperationAlert({
          type: 'success',
          message: 'No state boundaries intersect with this polygon.',
        });
        return;
      }

      const splitFeatures = splitResult.data.features.map((feature, index) => ({
        ...feature,
        properties: {
          ...feature.properties,
          appFeatureId: `${appFeatureId}-piece-${Date.now()}-${index}`,
        },
      }));

      recordHistorySnapshot();
      setDisplayData((previous) => ({
        type: 'FeatureCollection',
        features: [
          ...previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
          ...splitFeatures,
        ],
      }));

      const map = mapRef.current;
      if (map && selectedFeatureIdRef.current === appFeatureId) {
        clearSelectedFeature(map);
      }

      closePolygonMenu();
      closeContextMenu();
      setError('');
      setOperationAlert({
        type: 'success',
        message:
          splitFeatures.length > 1
            ? `Split complete. Created ${splitFeatures.length} state pieces.`
            : 'Split complete. No additional state pieces were created.',
      });
    } catch {
      setError('Split failed. Could not split the selected polygon by state.');
      setOperationAlert({
        type: 'error',
        message: 'Split failed. Could not split the selected polygon by state.',
      });
    } finally {
      setSplittingFeatureIds((previous) => {
        const next = new Set(previous);
        next.delete(appFeatureId);
        return next;
      });
    }
  }

  function handleSeparatePartsById(appFeatureId: string) {
    const targetFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    if (!targetFeature || targetFeature.geometry?.type !== 'MultiPolygon') {
      return;
    }

    const separatedParts = separatePolygonParts(targetFeature as Parameters<typeof separatePolygonParts>[0]);
    if (separatedParts.length <= 1) {
      return;
    }

    const baseName = polygonNameById[appFeatureId] || getPolygonDefaultName(targetFeature, 0);
    const replacementFeatures = separatedParts.map((feature, index) => ({
      ...feature,
      properties: {
        ...feature.properties,
        appFeatureId: `${appFeatureId}-part-${Date.now()}-${index}`,
        polygonName: `${baseName} Part ${index + 1}`,
      },
    }));

    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: [
        ...previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
        ...replacementFeatures,
      ],
    }));

    setPolygonNames((previous) => {
      const next = { ...previous };
      delete next[appFeatureId];

      replacementFeatures.forEach((feature, index) => {
        const nextId = feature.properties?.appFeatureId;
        if (typeof nextId === 'string') {
          next[nextId] = `${baseName} Part ${index + 1}`;
        }
      });

      return next;
    });

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current === appFeatureId) {
      clearSelectedFeature(map);
    }

    closeSmoothPanel();
    closePolygonMenu();
    closeContextMenu();
    setError('');
  }

  function handleDeleteFeatureById(appFeatureId: string) {
    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
    }));

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current === appFeatureId) {
      clearSelectedFeature(map);
    }

    closePolygonMenu();
    if (smoothPanel.appFeatureId === appFeatureId) {
      closeSmoothPanel();
    }
    if (polygonGeometryEditRef.current.appFeatureId === appFeatureId) {
      closePolygonGeometryEdit();
    }
    closeContextMenu();
  }

  function handleFocusPolygon(appFeatureId: string) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target) {
      return;
    }

    const map = mapRef.current;
    if (selectedFeatureId === appFeatureId) {
      if (map) clearSelectedFeature(map);
      closePolygonMenu();
      return;
    }

    if (map) {
      setSelectedFeature(map, appFeatureId);
    }

    fitMapToCollection({
      type: 'FeatureCollection',
      features: [target],
    });
    closePolygonMenu();
  }

  function handlePolygonNameChange(appFeatureId: string, name: string) {
    recordHistorySnapshot();
    setPolygonNames((previous) => ({
      ...previous,
      [appFeatureId]: name,
    }));
  }

  function handleExportPolygon(appFeatureId: string) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target || !isPolygonFeature(target as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const targetName = polygonNameById[appFeatureId] || 'polygon';
    const fileNameStem = sanitizeFileName(targetName);
    const payload: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: [
        {
          ...target,
          properties: {
            ...target.properties,
            polygonName: targetName,
          },
        },
      ],
    };

    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/geo+json' });
    const href = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = href;
    link.download = `${fileNameStem || 'polygon'}.geojson`;
    link.click();
    URL.revokeObjectURL(href);
  }

  function handleSaveContextMenuRename() {
    if (!contextMenu.appFeatureId) {
      return;
    }

    handlePolygonNameChange(contextMenu.appFeatureId, contextMenu.nameDraft);
    closeContextMenu();
  }

  const isUploadBusy = isHandlingUploads || isRestoringWorkspace;
  const activeUploadStatusMessage = isRestoringWorkspace
    ? 'Restoring saved workspace from this browser...'
    : uploadStatusMessage || 'Processing files...';

  return (
    <div className="flex h-full min-h-screen bg-[#f2f4f7] text-slate-900">
      <aside className="flex w-full max-w-107.5 flex-col border-r border-slate-200 bg-linear-to-b from-[#fffdf8] to-[#f3f5ff] p-5 lg:p-6">
        <div className="mb-5">
          <p className="flex items-center gap-1.5 text-xs font-semibold uppercase tracking-[0.25em] text-orange-700">
            <Braces className="h-3.5 w-3.5" />
            GeoJSON Workspace
          </p>
          <h1 className="mt-3 text-4xl font-black leading-[0.92] tracking-tight text-slate-900">
            Multi-file polygon operations.
          </h1>
          <p className="mt-3 text-sm text-slate-600">
            Upload multiple files and manage each polygon independently in the list or directly on the map.
          </p>
        </div>

        <section className="space-y-3 rounded-2xl border border-slate-200 bg-white/85 p-4 shadow-sm">
          <label className="flex items-center gap-1.5 text-xs font-semibold uppercase tracking-wide text-slate-600">
            <FileUp className="h-3.5 w-3.5" />
            Upload Files
          </label>
          <div
            role="button"
            tabIndex={0}
            onClick={handleUploadDropZoneClick}
            aria-disabled={isUploadBusy}
            onKeyDown={(event) => {
              if (isUploadBusy) {
                return;
              }

              if (event.key === 'Enter' || event.key === ' ') {
                event.preventDefault();
                handleUploadDropZoneClick();
              }
            }}
            onDragEnter={handleUploadDragEnter}
            onDragOver={handleUploadDragOver}
            onDragLeave={handleUploadDragLeave}
            onDrop={handleUploadDrop}
            className={`group block cursor-pointer rounded-xl border-2 border-dashed p-4 transition ${
              isUploadBusy
                ? 'cursor-wait border-indigo-300 bg-indigo-50/70 opacity-80'
                : isDragOverUpload
                ? 'border-indigo-500 bg-indigo-100/60 ring-2 ring-indigo-200'
                : 'border-slate-300 bg-slate-50/70 hover:border-indigo-400 hover:bg-indigo-50/50'
            }`}
          >
            <div className="flex items-start gap-3">
              <div
                className={`rounded-lg bg-white p-2 text-slate-700 shadow-sm ring-1 ring-slate-200 transition ${
                  isUploadBusy
                    ? 'text-indigo-700 ring-indigo-200'
                    : isDragOverUpload
                    ? 'scale-105 text-indigo-700 ring-indigo-300'
                    : ''
                }`}
              >
                {isUploadBusy ? <Loader2 className="h-5 w-5 animate-spin" /> : <FileUp className="h-5 w-5" />}
              </div>
              <div>
                <p
                  className={`text-sm font-semibold ${
                    isUploadBusy ? 'text-indigo-800' : isDragOverUpload ? 'text-indigo-800' : 'text-slate-800'
                  }`}
                >
                  {isUploadBusy ? activeUploadStatusMessage : isDragOverUpload ? 'Release to upload files' : 'Drop GeoJSON or CSV files here'}
                </p>
                <p className={`text-xs ${isUploadBusy || isDragOverUpload ? 'text-indigo-700' : 'text-slate-500'}`}>
                  {isUploadBusy
                    ? 'Large files can take a moment to parse, classify, and render.'
                    : isDragOverUpload
                    ? 'Files will be imported and mapped immediately'
                    : 'or click to browse device files'}
                </p>
              </div>
            </div>
          </div>
          <input
            ref={fileInputRef}
            type="file"
            multiple
            accept=".json,.geojson,.csv,application/geo+json,application/json,text/csv"
            onChange={handleFileChange}
            className="hidden"
          />

          {isUploadBusy ? (
            <p role="status" className="flex items-center gap-2 text-sm font-semibold text-indigo-700">
              <Loader2 className="h-4 w-4 animate-spin" />
              {activeUploadStatusMessage}
            </p>
          ) : null}

          <div className="flex items-center justify-between rounded-lg border border-slate-200 bg-slate-50 px-3 py-2">
            <span className="inline-flex items-center gap-1.5 text-sm font-medium text-slate-700">
              <MapPinned className="h-4 w-4" />
              Show state boundaries
            </span>
            <button
              type="button"
              role="switch"
              aria-checked={showStates}
              onClick={() => setShowStates((previous) => !previous)}
              className={`relative h-7 w-12 rounded-full transition ${showStates ? 'bg-slate-900' : 'bg-slate-300'}`}
            >
              <span
                className={`absolute top-1 h-5 w-5 rounded-full bg-white transition ${showStates ? 'left-6' : 'left-1'}`}
              />
            </button>
          </div>

          {error ? <p className="text-sm font-semibold text-red-700">{error}</p> : null}
          {isSplittingAll || splittingFeatureIds.size > 0 ? (
            <p role="status" className="text-sm font-semibold text-indigo-700">
              Splitting polygons by state boundaries...
            </p>
          ) : null}
          {operationAlert ? (
            <p
              role="alert"
              className={`text-sm font-semibold ${
                operationAlert.type === 'success' ? 'text-emerald-700' : 'text-red-700'
              }`}
            >
              {operationAlert.message}
            </p>
          ) : null}

          {polygonDraw.open ? (
            <div className="rounded-lg border border-blue-200 bg-blue-50 px-3 py-2">
              <p className="text-xs font-semibold uppercase tracking-wide text-blue-700">Drawing New Polygon</p>
              <p className="mt-1 text-xs text-blue-700">
                {polygonDraw.sourceFileName}: click map to add vertices ({polygonDraw.coordinates.length} added).
              </p>
              <div className="mt-2 flex items-center gap-2">
                <button
                  type="button"
                  onClick={finishPolygonDraw}
                  disabled={polygonDraw.coordinates.length < 3}
                  className="inline-flex items-center gap-1 rounded-md bg-blue-700 px-2.5 py-1.5 text-xs font-semibold text-white transition hover:bg-blue-600 disabled:cursor-not-allowed disabled:bg-blue-300"
                >
                  <Check className="h-3.5 w-3.5" />
                  Finish
                </button>
                <button
                  type="button"
                  onClick={closePolygonDraw}
                  className="inline-flex items-center gap-1 rounded-md border border-blue-300 bg-white px-2.5 py-1.5 text-xs font-semibold text-blue-700 transition hover:bg-blue-100"
                >
                  <X className="h-3.5 w-3.5" />
                  Cancel
                </button>
              </div>
            </div>
          ) : null}
        </section>

        <section className="mt-4 flex min-h-0 flex-1 flex-col rounded-2xl border border-slate-200 bg-white/85 p-4 shadow-sm">
          <div className="flex flex-wrap items-start justify-between gap-3">
            <div>
              <h2 className="inline-flex items-center gap-1.5 text-sm font-bold uppercase tracking-wide text-slate-700">
                <FolderTree className="h-4 w-4" />
                Files and Polygons
              </h2>
              <p className="mt-1 text-xs text-slate-500">Split, rename, export, or remove polygons by file.</p>
            </div>

            <div className="flex w-full gap-2">
              <ToolbarActionButton
                onClick={handleUndo}
                disabled={!undoStack.length}
                ariaLabel="Undo"
                tooltip="Undo (Cmd+Z)"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-slate-300 bg-white text-slate-700 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:border-slate-200 disabled:bg-slate-100 disabled:text-slate-400"
              >
                <Undo2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleRedo}
                disabled={!redoStack.length}
                ariaLabel="Redo"
                tooltip="Redo (Cmd+Shift+Z)"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-slate-300 bg-white text-slate-700 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:border-slate-200 disabled:bg-slate-100 disabled:text-slate-400"
              >
                <Redo2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleSplitAll}
                disabled={!polygonItems.length || isSplittingAll || splittingFeatureIds.size > 0}
                ariaLabel={isSplittingAll || splittingFeatureIds.size > 0 ? 'Splitting polygons' : 'Split All by State'}
                tooltip={isSplittingAll || splittingFeatureIds.size > 0 ? 'Splitting...' : 'Split All by State'}
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-indigo-200 bg-indigo-50 text-indigo-700 transition hover:bg-indigo-100 disabled:cursor-not-allowed disabled:border-indigo-100 disabled:bg-indigo-50/60 disabled:text-indigo-300"
              >
                {isSplittingAll || splittingFeatureIds.size > 0 ? (
                  <Loader2 className="h-4 w-4 animate-spin" />
                ) : (
                  <Scissors className="h-4 w-4" />
                )}
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleClearAll}
                disabled={!uploadedFiles.length && !csvPointData.features.length}
                ariaLabel="Clear All Files"
                tooltip="Clear All Files"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-red-200 bg-red-50 text-red-700 transition hover:bg-red-100 disabled:cursor-not-allowed disabled:border-red-100 disabled:bg-red-50/60 disabled:text-red-300"
              >
                <Trash2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleSmoothAll}
                disabled={!polygonItems.length}
                ariaLabel="Simplify All Polygons"
                tooltip="Simplify All Polygons"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg bg-teal-100 text-teal-800 transition hover:bg-teal-200 disabled:cursor-not-allowed disabled:bg-slate-100 disabled:text-slate-400"
              >
                <PenLine className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={toggleMergeMode}
                disabled={polygonItems.length < 2}
                ariaLabel={mergeMode ? 'Cancel Merge' : 'Merge Polygons'}
                tooltip={mergeMode ? 'Cancel Merge' : 'Merge Polygons'}
                className={`inline-flex h-9 w-full items-center justify-center rounded-lg transition disabled:cursor-not-allowed ${
                  mergeMode
                    ? 'bg-violet-700 text-white hover:bg-violet-600 disabled:bg-violet-300'
                    : 'bg-violet-100 text-violet-800 hover:bg-violet-200 disabled:bg-slate-100 disabled:text-slate-400'
                }`}
              >
                {mergeMode ? <X className="h-4 w-4" /> : <Merge className="h-4 w-4" />}
              </ToolbarActionButton>
            </div>
          </div>

          {mergeMode && (
            <div className="mt-3 flex items-center justify-between rounded-lg border border-violet-200 bg-violet-50 px-3 py-2">
              <span className="text-xs text-violet-700">
                {selectedForMerge.size < 2
                  ? `Select ${2 - selectedForMerge.size} more polygon${selectedForMerge.size === 1 ? '' : 's'}`
                  : `${selectedForMerge.size} polygons selected`}
              </span>
              <button
                onClick={handleMergeSelected}
                disabled={selectedForMerge.size < 2}
                className="inline-flex items-center gap-1 rounded-md bg-violet-700 px-2.5 py-1.5 text-xs font-semibold text-white transition hover:bg-violet-600 disabled:cursor-not-allowed disabled:bg-violet-300"
              >
                <Merge className="h-3.5 w-3.5" />
                Merge {selectedForMerge.size > 0 ? selectedForMerge.size : ''} Selected
              </button>
            </div>
          )}

          {csvPointFiles.length > 0 ? (
            <div className="mt-3 rounded-xl border border-emerald-100 bg-linear-to-br from-emerald-50 via-white to-amber-50 p-3">
              <button
                type="button"
                onClick={() => setIsCsvLegendExpanded((previous) => !previous)}
                className="flex w-full items-center justify-between gap-3 text-left"
                aria-expanded={isCsvLegendExpanded}
                aria-controls="csv-boundary-legend"
              >
                <div>
                  <p className="text-[11px] font-semibold uppercase tracking-[0.18em] text-slate-600">CSV Boundary Legend</p>
                  <p className="mt-1 text-xs text-slate-600">Point and cluster colors update as GeoJSON boundaries change.</p>
                </div>
                <span className="inline-flex p-2 items-center justify-center rounded-lg bg-white/80 text-slate-700 ring-1 ring-slate-200">
                  {isCsvLegendExpanded ? <ChevronUp className="h-4 w-4" /> : <ChevronDown className="h-4 w-4" />}
                </span>
              </button>

              <AnimatePresence initial={false}>
                {isCsvLegendExpanded ? (
                  <motion.div
                    id="csv-boundary-legend"
                    initial={{ height: 0, opacity: 0, y: -6 }}
                    animate={{ height: 'auto', opacity: 1, y: 0 }}
                    exit={{ height: 0, opacity: 0, y: -6 }}
                    transition={{ duration: 0.18, ease: 'easeOut' }}
                    className="overflow-hidden"
                  >
                    <div className="mt-3 grid gap-2 text-xs text-slate-700">
                      <div className="flex items-center gap-2">
                        <span className="h-2.5 w-2.5 rounded-full bg-emerald-600 ring-2 ring-emerald-100" />
                        <span>Inside at least one GeoJSON boundary</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2.5 w-2.5 rounded-full bg-red-600 ring-2 ring-red-100" />
                        <span>Outside all GeoJSON boundaries</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2.5 w-2.5 rounded-full bg-amber-400 ring-2 ring-amber-100" />
                        <span>Mixed cluster with inside and outside points</span>
                      </div>
                    </div>
                  </motion.div>
                ) : null}
              </AnimatePresence>

              <div className="mt-3 space-y-1">
                {csvPointFiles.map((csvFile) => (
                  <div
                    key={csvFile.id}
                    className="flex items-center justify-between rounded-lg bg-white/90 px-2.5 py-2 ring-1 ring-slate-200"
                  >
                    <div className="min-w-0">
                      <p className="truncate text-sm font-medium text-slate-800" title={csvFile.name}>
                        {csvFile.name}
                      </p>
                      <p className="text-[11px] text-slate-500">{csvFile.pointCount.toLocaleString()} coordinate points</p>
                    </div>
                    <button
                      type="button"
                      onClick={() => handleRemoveCsvPointFile(csvFile.id)}
                      aria-label={`Remove ${csvFile.name}`}
                      title={`Remove ${csvFile.name}`}
                      className="ml-3 inline-flex h-8 w-8 shrink-0 items-center justify-center rounded-md text-red-600 transition hover:bg-red-50"
                    >
                      <Trash2 className="h-4 w-4" />
                    </button>
                  </div>
                ))}
              </div>
            </div>
          ) : null}

          <div className="mt-3 space-y-3 overflow-y-auto pr-1">
            {filesWithPolygons.length === 0 ? (
              <p className="flex h-full w-full rounded-lg items-center justify-center border border-dashed border-slate-300 bg-slate-50 p-3 text-sm text-slate-500">
                {csvPointFiles.length > 0 ? 'No GeoJSON polygon files loaded yet.' : 'No files loaded yet.'}
              </p>
            ) : (
              filesWithPolygons.map((group) => (
                <article key={group.id} className="rounded-xl border border-slate-200 bg-slate-50 p-3 overflow-visible">
                  <div className="mb-3 flex items-start justify-between gap-2">
                    <div>
                      <p className="max-w-55 truncate text-sm font-bold text-slate-900">{group.name}</p>
                      <p className="text-xs text-slate-500">
                        {group.featureCount} features, {group.polygons.length} polygons currently visible
                      </p>
                    </div>
                    <div className="flex items-center gap-1">
                      <button
                        onClick={() => handleAddPolygonToFile(group.id, group.name)}
                        className="inline-flex items-center gap-1 rounded-lg border border-emerald-200 bg-emerald-50 p-2 text-xs font-semibold text-emerald-700 transition hover:bg-emerald-100"
                        title={`Draw polygon in ${group.name}`}
                        aria-label={`Draw polygon in ${group.name}`}
                      >
                        <Plus className="h-3.5 w-3.5" />
                      </button>
                      <button
                        onClick={() => handleRemoveFile(group.id)}
                        className="inline-flex items-center gap-1 rounded-lg border border-red-200 bg-red-50 p-2 text-xs font-semibold text-red-700 transition hover:bg-red-200"
                      >
                        <Trash2 className="h-3.5 w-3.5" />
                      </button>
                    </div>
                  </div>

                  <div className="space-y-2">
                    {group.polygons.length === 0 ? (
                      <p className="flex h-full w-full rounded-lg items-center justify-center border border-dashed border-slate-300 bg-white p-2 text-xs text-slate-500">
                        No polygons from this file are currently visible.
                      </p>
                    ) : (
                      group.polygons.map((item, index) => {
                        const isChecked = selectedForMerge.has(item.appFeatureId);
                        const isSelected = !mergeMode && selectedFeatureId === item.appFeatureId;
                        const isSplitBusy = splittingFeatureIds.has(item.appFeatureId);
                        const isGeometryEditActive =
                          polygonGeometryEdit.open && polygonGeometryEdit.appFeatureId === item.appFeatureId;
                        const isCollapsed = collapsedPolygonIds.has(item.appFeatureId);
                        const metrics = polygonMetricsById[item.appFeatureId] || { vertices: 0, edges: 0 };
                        const polygonColor = isSelected
                          ? POLYGON_SELECTED_FILL_COLOR
                          : polygonColorById[item.appFeatureId] || getPolygonColorForId(item.appFeatureId);
                        return (
                        <div
                          key={item.appFeatureId}
                          data-appfeatureid={item.appFeatureId}
                          onClick={() => mergeMode ? toggleSelectForMerge(item.appFeatureId) : handleFocusPolygon(item.appFeatureId)}
                          className={`relative rounded-lg border p-2.5 transition ${
                            mergeMode && isChecked
                              ? 'border-violet-400 bg-violet-50 ring-1 ring-violet-300'
                              : isSelected
                              ? 'border-amber-400 bg-amber-50 ring-1 ring-amber-300'
                              : 'border-slate-200 bg-white hover:border-indigo-300 hover:bg-indigo-50/40'
                          } ${mergeMode ? 'cursor-pointer' : ''}`}
                        >
                          <div className="flex items-center justify-between gap-2">
                            {mergeMode ? (
                              <div className="flex items-center gap-2">
                                <input
                                  type="checkbox"
                                  checked={isChecked}
                                  onChange={() => toggleSelectForMerge(item.appFeatureId)}
                                  onClick={(event) => event.stopPropagation()}
                                  className="h-4 w-4 cursor-pointer accent-violet-700"
                                />
                                <p className="inline-flex items-center gap-1 truncate text-[11px] font-semibold uppercase tracking-wide text-violet-700">
                                  <Tag className="h-3 w-3" />
                                  Polygon {index + 1}
                                </p>
                              </div>
                            ) : (
                              <div className="flex items-center gap-1">
                                <span
                                  aria-hidden="true"
                                  className="h-2.5 w-2.5 rounded-full ring-1 ring-slate-300"
                                  style={{ backgroundColor: polygonColor }}
                                />
                                <p className="truncate text-[11px] font-semibold uppercase tracking-wide text-slate-500">
                                  Polygon {index + 1}
                                </p>
                                {!isGeometryEditActive ? (
                                  <button
                                    onClick={(event) => {
                                      event.stopPropagation();
                                      startPolygonEditSession(item.appFeatureId);
                                    }}
                                    title="Edit vertices"
                                    aria-label="Edit polygon vertices"
                                    className="inline-flex p-1 items-center justify-center rounded-md text-slate-500 transition hover:bg-slate-100 hover:text-slate-700"
                                  >
                                    <Pencil className="h-3 w-3" />
                                  </button>
                                ) : null}
                              </div>
                            )}
                            {item.splitByState && item.stateBadge ? (
                              <span className="rounded-full bg-orange-100 px-2 py-0.5 text-[10px] font-bold uppercase tracking-wide text-orange-700">
                                {item.stateBadge}
                              </span>
                            ) : null}

                            {!mergeMode && (
                              <div className="ml-auto flex items-center gap-1" onClick={(event) => event.stopPropagation()}>
                                <PolygonIconActionButton
                                  onClick={() => void handleSplitFeatureById(item.appFeatureId)}
                                  tooltip={isSplitBusy ? 'Splitting...' : 'Split by State'}
                                  ariaLabel={isSplitBusy ? 'Splitting polygon by state' : 'Split by State'}
                                  disabled={isSplitBusy}
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-indigo-200 bg-indigo-50 text-indigo-700 transition hover:bg-indigo-100"
                                >
                                  {isSplitBusy ? <Loader2 className="h-3 w-3 animate-spin" /> : <Scissors className="h-3 w-3" />}
                                </PolygonIconActionButton>
                                {item.isMultiPolygon ? (
                                  <PolygonIconActionButton
                                    onClick={() => handleSeparatePartsById(item.appFeatureId)}
                                    tooltip="Separate Parts"
                                    ariaLabel="Separate Parts"
                                    className="inline-flex p-1 items-center justify-center rounded-md border border-sky-200 bg-sky-50 text-sky-700 transition hover:bg-sky-100"
                                  >
                                    <Braces className="h-3 w-3" />
                                  </PolygonIconActionButton>
                                ) : null}
                                <PolygonIconActionButton
                                  onClick={() => handleExportPolygon(item.appFeatureId)}
                                  tooltip="Export"
                                  ariaLabel="Export"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-emerald-200 bg-emerald-50 text-emerald-700 transition hover:bg-emerald-100"
                                >
                                  <Download className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={(event) => openSmoothPanelForFeature(item.appFeatureId, event.currentTarget)}
                                  tooltip="Smooth"
                                  ariaLabel="Smooth"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-teal-200 bg-teal-50 text-teal-700 transition hover:bg-teal-100"
                                >
                                  <PenLine className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={() => handleDeleteFeatureById(item.appFeatureId)}
                                  tooltip="Remove"
                                  ariaLabel="Remove"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-red-200 bg-red-50 text-red-700 transition hover:bg-red-100"
                                >
                                  <Trash2 className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={() => togglePolygonExpanded(item.appFeatureId)}
                                  tooltip={isCollapsed ? 'Expand Details' : 'Collapse Details'}
                                  ariaLabel={isCollapsed ? 'Expand polygon details' : 'Collapse polygon details'}
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-slate-200 bg-slate-50 text-slate-700 transition hover:bg-slate-100"
                                >
                                  {isCollapsed ? <ChevronDown className="h-3 w-3" /> : <ChevronUp className="h-3 w-3" />}
                                </PolygonIconActionButton>
                              </div>
                            )}
                          </div>

                          <AnimatePresence initial={false}>
                            {!isCollapsed ? (
                              <motion.div
                                key={`details-${item.appFeatureId}`}
                                initial={{ height: 0, opacity: 0 }}
                                animate={{ height: 'auto', opacity: 1 }}
                                exit={{ height: 0, opacity: 0 }}
                                transition={{ duration: 0.2, ease: 'easeInOut' }}
                                className="overflow-hidden"
                              >
                              {isGeometryEditActive ? (
                                <p className="mt-1 rounded-md border border-amber-200 bg-amber-50 px-2 py-1 text-[11px] font-semibold text-amber-700">
                                  Drag vertices to move, hover and click near edges to insert vertices, and right-click (or Shift-click) a vertex to delete. Snapping guides are enabled.
                                </p>
                              ) : null}
                              <div className="mt-1 flex items-center gap-1" onClick={(event) => event.stopPropagation()}>
                                {editingPolygonId === item.appFeatureId ? (
                                  <>
                                    <input
                                      value={editingPolygonNameDraft}
                                      onChange={(event) => setEditingPolygonNameDraft(event.target.value)}
                                      onClick={(event) => event.stopPropagation()}
                                      className="w-full rounded-lg border border-slate-300 bg-white px-2.5 py-2 text-sm text-slate-900"
                                      placeholder="Polygon name"
                                    />
                                    <button
                                      onClick={(event) => {
                                        event.stopPropagation();
                                        void savePolygonEditSession(item.appFeatureId);
                                      }}
                                      title={savingPolygonEditId === item.appFeatureId ? 'Saving edits' : 'Save edits'}
                                      aria-label={savingPolygonEditId === item.appFeatureId ? 'Saving edits' : 'Save edits'}
                                      disabled={savingPolygonEditId === item.appFeatureId}
                                      className="inline-flex p-2 items-center justify-center rounded-md bg-emerald-600 text-white transition hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-emerald-400"
                                    >
                                      {savingPolygonEditId === item.appFeatureId ? (
                                        <Loader2 className="h-4.5 w-4.5 animate-spin" />
                                      ) : (
                                        <Check className="h-4.5 w-4.5" />
                                      )}
                                    </button>
                                    <button
                                      onClick={(event) => {
                                        event.stopPropagation();
                                        cancelPolygonEditSession(item.appFeatureId);
                                      }}
                                      title="Cancel rename"
                                      aria-label="Cancel rename"
                                      disabled={savingPolygonEditId === item.appFeatureId}
                                      className="inline-flex p-2 items-center justify-center rounded-md border border-slate-300 text-slate-700 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:opacity-60"
                                    >
                                      <X className="h-4.5 w-4.5" />
                                    </button>
                                  </>
                                ) : (
                                  <p className="w-full mt-2 truncate rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-sm text-slate-700">
                                    {polygonNameById[item.appFeatureId] || item.defaultName}
                                  </p>
                                )}
                              </div>

                              <div className="mt-2 grid grid-cols-2 gap-2" onClick={(event) => event.stopPropagation()}>
                                <div className="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2">
                                  <p className="text-[10px] font-semibold uppercase tracking-wide text-slate-500">Vertices</p>
                                  <p className="mt-0.5 text-sm font-bold text-slate-800">{metrics.vertices}</p>
                                </div>
                                <div className="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2">
                                  <p className="text-[10px] font-semibold uppercase tracking-wide text-slate-500">Edges</p>
                                  <p className="mt-0.5 text-sm font-bold text-slate-800">{metrics.edges}</p>
                                </div>
                              </div>
                              </motion.div>
                            ) : null}
                          </AnimatePresence>
                        </div>
                        );
                      })
                    )}
                  </div>
                </article>
              ))
            )}
          </div>
        </section>
      </aside>

      {smoothPanel.open ? (
        <div className="fixed inset-0 z-35" onClick={closeSmoothPanel}>
          <div
            className="absolute w-72 max-h-[calc(100vh-2rem)] overflow-y-auto rounded-xl border border-slate-300 bg-white p-3 shadow-2xl"
            style={{
              left: `${smoothPanel.x}px`,
              top: `${smoothPanel.y}px`,
            }}
            onClick={(event) => event.stopPropagation()}
          >
            <p className="text-xs font-bold uppercase tracking-wide text-slate-500">Polygon Geometry</p>
            <p className="mt-1 text-xs text-slate-600">Preview shape changes live. Apply commits them.</p>

            <label className="mt-3 block text-[11px] font-semibold uppercase tracking-wide text-slate-500">
              Algorithm
            </label>
            <select
              value={smoothPanel.algorithm}
              onChange={(event) =>
                setSmoothPanel((previous) => ({
                  ...previous,
                  algorithm: event.target.value as SmoothAlgorithm,
                }))
              }
              className="mt-1 w-full rounded-md border border-slate-300 bg-white px-2 py-1.5 text-sm text-slate-800"
            >
              <option value="simplify">Simplify (reduce vertices)</option>
              <option value="chaikin">Chaikin (corner-cutting)</option>
              <option value="moving-average">Moving average</option>
              <option value="midpoint-subdivide">Midpoint subdivide</option>
            </select>

            <div className="mt-3">
              <div className="flex items-center justify-between text-[11px] font-semibold uppercase tracking-wide text-slate-500">
                <span>{smoothPanel.algorithm === 'simplify' ? 'Simplify Amount' : 'Sensitivity'}</span>
                <span>{smoothPanel.sensitivity}</span>
              </div>
              <input
                type="range"
                min={0}
                max={100}
                step={1}
                value={smoothPanel.sensitivity}
                onChange={(event) =>
                  setSmoothPanel((previous) => ({
                    ...previous,
                    sensitivity: Number(event.target.value),
                  }))
                }
                className="mt-1 w-full accent-teal-600"
              />
              <p className="mt-1 text-[11px] text-slate-500">
                {smoothPanel.algorithm === 'simplify'
                  ? 'Higher values remove more vertices.'
                  : 'Higher values create a stronger smoothing effect.'}
              </p>

              {smoothGeometryMetrics ? (
                <div className="mt-3 grid grid-cols-2 gap-2 text-[11px]">
                  <div className="rounded-md border border-slate-200 bg-slate-50 px-2 py-1.5">
                    <p className="font-semibold uppercase tracking-wide text-slate-500">Vertices</p>
                    <p className="text-sm font-bold text-slate-800">
                      {smoothGeometryMetrics.preview.vertices}
                      <span className="ml-1 text-[11px] font-medium text-slate-500">
                        ({smoothGeometryMetrics.preview.vertices - smoothGeometryMetrics.original.vertices >= 0
                          ? '+'
                          : ''}
                        {smoothGeometryMetrics.preview.vertices - smoothGeometryMetrics.original.vertices})
                      </span>
                    </p>
                  </div>
                  <div className="rounded-md border border-slate-200 bg-slate-50 px-2 py-1.5">
                    <p className="font-semibold uppercase tracking-wide text-slate-500">Edges</p>
                    <p className="text-sm font-bold text-slate-800">
                      {smoothGeometryMetrics.preview.edges}
                      <span className="ml-1 text-[11px] font-medium text-slate-500">
                        ({smoothGeometryMetrics.preview.edges - smoothGeometryMetrics.original.edges >= 0
                          ? '+'
                          : ''}
                        {smoothGeometryMetrics.preview.edges - smoothGeometryMetrics.original.edges})
                      </span>
                    </p>
                  </div>
                </div>
              ) : null}
            </div>

            <div className="mt-4 flex justify-end gap-2">
              <button
                onClick={closeSmoothPanel}
                className="rounded-md border border-slate-300 px-2.5 py-1.5 text-xs font-semibold text-slate-700 transition hover:bg-slate-50"
              >
                Cancel
              </button>
              <button
                onClick={applySmoothToFeature}
                className="rounded-md bg-teal-600 px-2.5 py-1.5 text-xs font-semibold text-white transition hover:bg-teal-500"
              >
                Apply Smoothing
              </button>
            </div>
          </div>
        </div>
      ) : null}

      <main className="relative flex-1 p-3 lg:p-4">
        <div
          ref={mapContainerRef}
          className="h-[58vh] w-full overflow-hidden rounded-3xl border border-slate-200 shadow-[0_28px_70px_rgba(15,23,42,0.18)] lg:h-[calc(100vh-2rem)]"
        />

        {contextMenu.open ? (
          <div
            className="absolute z-20 grid min-w-65 gap-2 rounded-xl border border-slate-300 bg-white p-2 shadow-2xl"
            style={{ left: `${contextMenu.x + 20}px`, top: `${contextMenu.y + 20}px` }}
            onClick={(event) => event.stopPropagation()}
          >
            <label className="inline-flex items-center gap-1.5 text-[11px] font-semibold uppercase tracking-wide text-slate-500">
              <Tag className="h-3.5 w-3.5" />
              Polygon Name
            </label>
            <input
              value={contextMenu.nameDraft}
              onChange={(event) =>
                setContextMenu((previous) => ({
                  ...previous,
                  nameDraft: event.target.value,
                }))
              }
              className="rounded-md border border-slate-300 px-2 py-1.5 text-sm"
              placeholder="Polygon name"
            />

            <div className="grid grid-cols-3 gap-1.5">
              <button
                onClick={handleSaveContextMenuRename}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-slate-200 px-2 py-2 text-xs font-medium text-slate-800 transition hover:bg-slate-300"
              >
                <PenLine className="h-3.5 w-3.5" />
                Rename
              </button>
              <button
                onClick={() => contextMenu.appFeatureId && void handleSplitFeatureById(contextMenu.appFeatureId)}
                disabled={
                  !contextMenu.appFeatureId ||
                  splittingFeatureIds.has(contextMenu.appFeatureId) ||
                  isSplittingAll
                }
                className="inline-flex items-center justify-center gap-1 rounded-md bg-indigo-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-indigo-500 disabled:cursor-not-allowed disabled:bg-indigo-300"
              >
                {contextMenu.appFeatureId && splittingFeatureIds.has(contextMenu.appFeatureId) ? (
                  <Loader2 className="h-3.5 w-3.5 animate-spin" />
                ) : (
                  <Scissors className="h-3.5 w-3.5" />
                )}
                {contextMenu.appFeatureId && splittingFeatureIds.has(contextMenu.appFeatureId)
                  ? 'Splitting...'
                  : 'Split by State'}
              </button>
              <button
                onClick={() => contextMenu.appFeatureId && handleDeleteFeatureById(contextMenu.appFeatureId)}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-red-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-red-500"
              >
                <Trash2 className="h-3.5 w-3.5" />
                Remove
              </button>
            </div>

            {contextMenu.appFeatureId &&
            polygonItems.find((item) => item.appFeatureId === contextMenu.appFeatureId)?.isMultiPolygon ? (
              <button
                onClick={() => handleSeparatePartsById(contextMenu.appFeatureId as string)}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-sky-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-sky-500"
              >
                <Braces className="h-3.5 w-3.5" />
                Separate Parts
              </button>
            ) : null}
          </div>
        ) : null}
      </main>
    </div>
  );
}
