import type { Feature, FeatureCollection, MultiPolygon, Polygon } from 'geojson';

type StateProperties = {
  STUSPS?: string;
  NAME?: string;
  name?: string;
};

type StateFeature = Feature<Polygon | MultiPolygon, StateProperties>;

const EMPTY_STATES: FeatureCollection<Polygon | MultiPolygon, StateProperties> = {
  type: 'FeatureCollection',
  features: [],
};

let cachedStates: FeatureCollection<Polygon | MultiPolygon, StateProperties> | null = null;
let cachedStatePromise: Promise<FeatureCollection<Polygon | MultiPolygon, StateProperties>> | null = null;

export async function getStateBoundaries(): Promise<FeatureCollection<Polygon | MultiPolygon, StateProperties>> {
  if (cachedStates) {
    return cachedStates;
  }

  if (cachedStatePromise) {
    return cachedStatePromise;
  }

  cachedStatePromise = fetch('/tiger2025-states.json')
    .then(async (response) => {
      if (!response.ok) {
        throw new Error(`Failed to load state boundaries (${response.status})`);
      }

      return (await response.json()) as FeatureCollection<Polygon | MultiPolygon, StateProperties>;
    })
    .then((data) => {
      if (data.type !== 'FeatureCollection' || !Array.isArray(data.features)) {
        throw new Error('Invalid state boundary GeoJSON format');
      }

      cachedStates = data;
      return data;
    })
    .catch((error) => {
      cachedStatePromise = null;
      throw error;
    });

  return cachedStatePromise;
}

export function getStateLabel(state: StateFeature, fallbackIndex: number): string {
  const name = state.properties?.NAME?.trim() || state.properties?.name?.trim();
  return name || `state-${fallbackIndex + 1}`;
}

export function getEmptyStateBoundaries(): FeatureCollection<Polygon | MultiPolygon, StateProperties> {
  return EMPTY_STATES;
}