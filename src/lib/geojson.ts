import type { Feature, GeoJsonProperties, Geometry, Polygon, MultiPolygon } from 'geojson';
import bbox from '@turf/bbox';
import booleanIntersects from '@turf/boolean-intersects';
import intersect from '@turf/intersect';
import simplify from '@turf/simplify';
import union from '@turf/union';
import { featureCollection } from '@turf/helpers';
import { flattenEach } from '@turf/meta';
import { getStateBoundaries, getStateLabel } from './stateBoundaries';
import type { AnyFeatureCollection, ImportSummary, SplitSummary } from '../types';

type PolygonFeature = Feature<Polygon | MultiPolygon, GeoJsonProperties>;

export type SmoothAlgorithm = 'chaikin' | 'moving-average' | 'midpoint-subdivide' | 'simplify';

export type SmoothOptions = {
  algorithm?: SmoothAlgorithm;
  sensitivity?: number;
  iterations?: number;
};

export function parseGeoJson(rawText: string): AnyFeatureCollection {
  const parsed = JSON.parse(rawText) as GeoJSON.GeoJSON;

  if (parsed.type === 'FeatureCollection') {
    return parsed as AnyFeatureCollection;
  }

  if (parsed.type === 'Feature') {
    return featureCollection([parsed as Feature<Geometry, GeoJsonProperties>]);
  }

  return featureCollection([
    {
      type: 'Feature',
      geometry: parsed as Geometry,
      properties: {},
    },
  ]);
}

export function summarizeGeoJson(data: AnyFeatureCollection): ImportSummary {
  const polygonCount = data.features.filter(
    (item) => item.geometry?.type === 'Polygon' || item.geometry?.type === 'MultiPolygon',
  ).length;

  return {
    featureCount: data.features.length,
    polygonCount,
  };
}

export function getCollectionBounds(data: AnyFeatureCollection): [number, number, number, number] | null {
  if (!data.features.length) {
    return null;
  }

  try {
    const [minX, minY, maxX, maxY] = bbox(data);
    return [minX, minY, maxX, maxY];
  } catch {
    return null;
  }
}

export async function splitPolygonsByStates(source: AnyFeatureCollection): Promise<{
  data: AnyFeatureCollection;
  summary: SplitSummary;
}> {
  const states = await getStateBoundaries();
  const splitFeatures: Feature<Geometry, GeoJsonProperties>[] = [];
  let originalPolygonCount = 0;
  let splitPolygonCount = 0;
  let untouchedPolygonCount = 0;
  let noIntersectionPolygonCount = 0;

  source.features.forEach((sourceFeature, sourceIndex) => {
    if (!sourceFeature.geometry) {
      splitFeatures.push(sourceFeature);
      return;
    }

    if (sourceFeature.geometry.type !== 'Polygon' && sourceFeature.geometry.type !== 'MultiPolygon') {
      splitFeatures.push(sourceFeature);
      return;
    }

    originalPolygonCount += 1;

    const polygonFeature = sourceFeature as PolygonFeature;
    const pieces: Feature<Polygon | MultiPolygon, GeoJsonProperties>[] = [];
    let didIntersectAnyState = false;

    states.features.forEach((state, stateIndex) => {
      if (!booleanIntersects(polygonFeature, state)) {
        return;
      }

      didIntersectAnyState = true;

      const clipped = intersect(featureCollection([polygonFeature, state]));
      if (!clipped || (clipped.geometry.type !== 'Polygon' && clipped.geometry.type !== 'MultiPolygon')) {
        return;
      }

      pieces.push({
        ...clipped,
        properties: {
          ...sourceFeature.properties,
          sourceFeatureIndex: sourceIndex,
          splitByState: true,
          stateName: getStateLabel(state, stateIndex),
        },
      });
    });

    if (!didIntersectAnyState) {
      noIntersectionPolygonCount += 1;
    }

    if (pieces.length <= 1) {
      untouchedPolygonCount += 1;
      splitFeatures.push({
        ...sourceFeature,
        properties: {
          ...sourceFeature.properties,
          sourceFeatureIndex: sourceIndex,
          splitByState: false,
        },
      });
      return;
    }

    splitPolygonCount += pieces.length;
    pieces.forEach((piece) => {
      flattenEach(piece, (flattened) => {
        splitFeatures.push(flattened as Feature<Geometry, GeoJsonProperties>);
      });
    });
  });

  return {
    data: featureCollection(splitFeatures),
    summary: {
      originalCount: originalPolygonCount,
      splitCount: splitPolygonCount,
      untouchedCount: untouchedPolygonCount,
      noIntersectionCount: noIntersectionPolygonCount,
    },
  };
}

export function mergePolygons(
  features: Feature<Polygon | MultiPolygon, GeoJsonProperties>[],
): Feature<Polygon | MultiPolygon, GeoJsonProperties> | null {
  if (features.length === 0) {
    return null;
  }

  if (features.length === 1) {
    return features[0];
  }

  let result: Feature<Polygon | MultiPolygon, GeoJsonProperties> = features[0];

  for (let i = 1; i < features.length; i++) {
    const merged = union(featureCollection([result, features[i]]));
    if (!merged) {
      return null;
    }
    result = merged;
  }

  return result;
}

export function separatePolygonParts(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
): Feature<Polygon, GeoJsonProperties>[] {
  if (feature.geometry.type === 'Polygon') {
    return [feature as Feature<Polygon, GeoJsonProperties>];
  }

  return feature.geometry.coordinates.map((coordinates, index, allCoordinates) => ({
    type: 'Feature',
    geometry: {
      type: 'Polygon',
      coordinates,
    },
    properties: {
      ...feature.properties,
      multipartSeparated: true,
      multipartPartIndex: index,
      multipartPartCount: allCoordinates.length,
    },
  }));
}

function clampSensitivity(value: number | undefined): number {
  if (typeof value !== 'number' || Number.isNaN(value)) {
    return 40;
  }

  return Math.max(0, Math.min(100, value));
}

function sensitivityToIterations(sensitivity: number): number {
  return Math.max(1, Math.min(6, Math.round(1 + sensitivity / 20)));
}

function sensitivityToSimplifyTolerance(sensitivity: number): number {
  if (sensitivity <= 0) {
    return 0;
  }

  return (sensitivity / 100) * 0.01;
}

function closeRing(points: number[][]): number[][] {
  if (!points.length) {
    return points;
  }

  return [...points, points[0]];
}

function toOpenRingSeed(ring: number[][]): number[][] {
  if (ring.length < 4) {
    return ring;
  }

  const first = ring[0];
  const last = ring[ring.length - 1];
  const isClosed = first[0] === last[0] && first[1] === last[1];
  return isClosed ? ring.slice(0, -1) : ring.slice();
}

function smoothRingChaikin(ring: number[][], iterations: number): number[][] {
  const seed = toOpenRingSeed(ring);

  if (seed.length < 3) {
    return ring;
  }

  let points = seed;

  for (let iter = 0; iter < iterations; iter++) {
    const next: number[][] = [];

    for (let i = 0; i < points.length; i++) {
      const current = points[i];
      const following = points[(i + 1) % points.length];

      const q: number[] = [
        current[0] * 0.75 + following[0] * 0.25,
        current[1] * 0.75 + following[1] * 0.25,
      ];
      const r: number[] = [
        current[0] * 0.25 + following[0] * 0.75,
        current[1] * 0.25 + following[1] * 0.75,
      ];

      next.push(q, r);
    }

    points = next;
  }

  return closeRing(points);
}

function smoothRingMovingAverage(ring: number[][], iterations: number, sensitivity: number): number[][] {
  const seed = toOpenRingSeed(ring);

  if (seed.length < 3) {
    return ring;
  }

  let points = seed;
  const alpha = 0.15 + (sensitivity / 100) * 0.35;

  for (let iter = 0; iter < iterations; iter++) {
    const next: number[][] = [];

    for (let i = 0; i < points.length; i++) {
      const prev = points[(i - 1 + points.length) % points.length];
      const current = points[i];
      const following = points[(i + 1) % points.length];

      next.push([
        current[0] * (1 - alpha) + ((prev[0] + following[0]) / 2) * alpha,
        current[1] * (1 - alpha) + ((prev[1] + following[1]) / 2) * alpha,
      ]);
    }

    points = next;
  }

  return closeRing(points);
}

function smoothRingMidpointSubdivide(ring: number[][], iterations: number, sensitivity: number): number[][] {
  const seed = toOpenRingSeed(ring);

  if (seed.length < 3) {
    return ring;
  }

  let points = seed;
  const blend = 0.25 + (sensitivity / 100) * 0.5;

  for (let iter = 0; iter < iterations; iter++) {
    const next: number[][] = [];

    for (let i = 0; i < points.length; i++) {
      const current = points[i];
      const following = points[(i + 1) % points.length];
      const midX = (current[0] + following[0]) / 2;
      const midY = (current[1] + following[1]) / 2;

      next.push([
        current[0] * (1 - blend) + midX * blend,
        current[1] * (1 - blend) + midY * blend,
      ]);
      next.push([
        following[0] * (1 - blend) + midX * blend,
        following[1] * (1 - blend) + midY * blend,
      ]);
    }

    points = next;
  }

  return closeRing(points);
}

function smoothRingCoordinates(ring: number[][], algorithm: SmoothAlgorithm, sensitivity: number, iterations: number): number[][] {
  if (algorithm === 'simplify') {
    return ring;
  }

  if (algorithm === 'moving-average') {
    return smoothRingMovingAverage(ring, iterations, sensitivity);
  }

  if (algorithm === 'midpoint-subdivide') {
    return smoothRingMidpointSubdivide(ring, iterations, sensitivity);
  }

  return smoothRingChaikin(ring, iterations);
}

export function smoothPolygonFeature(
  feature: Feature<Polygon | MultiPolygon, GeoJsonProperties>,
  options: SmoothOptions = {},
): Feature<Polygon | MultiPolygon, GeoJsonProperties> {
  const sensitivity = clampSensitivity(options.sensitivity);
  const algorithm = options.algorithm ?? 'chaikin';
  const iterations = options.iterations ?? sensitivityToIterations(sensitivity);

  if (algorithm === 'simplify') {
    if (sensitivity <= 0) {
      return feature;
    }

    const simplified = simplify(feature, {
      tolerance: sensitivityToSimplifyTolerance(sensitivity),
      highQuality: true,
      mutate: false,
    });

    return {
      ...simplified,
      properties: {
        ...feature.properties,
        ...simplified.properties,
      },
    } as Feature<Polygon | MultiPolygon, GeoJsonProperties>;
  }

  if (feature.geometry.type === 'Polygon') {
    return {
      ...feature,
      geometry: {
        ...feature.geometry,
        coordinates: feature.geometry.coordinates.map((ring) =>
          smoothRingCoordinates(ring, algorithm, sensitivity, iterations),
        ),
      },
    };
  }

  return {
    ...feature,
    geometry: {
      ...feature.geometry,
      coordinates: feature.geometry.coordinates.map((polygon) =>
        polygon.map((ring) => smoothRingCoordinates(ring, algorithm, sensitivity, iterations)),
      ),
    },
  };
}

export function smoothPolygonsInCollection(source: AnyFeatureCollection, options: SmoothOptions = {}): AnyFeatureCollection {
  return {
    ...source,
    features: source.features.map((feature) => {
      if (!feature.geometry) {
        return feature;
      }

      if (feature.geometry.type !== 'Polygon' && feature.geometry.type !== 'MultiPolygon') {
        return feature;
      }

      return smoothPolygonFeature(feature as Feature<Polygon | MultiPolygon, GeoJsonProperties>, options);
    }),
  };
}