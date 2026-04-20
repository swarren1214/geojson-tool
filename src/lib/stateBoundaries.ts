import type { Feature, FeatureCollection, MultiPolygon, Polygon } from 'geojson';
import { feature } from 'topojson-client';
import usStates from 'us-atlas/states-10m.json';

type StateProperties = {
  name?: string;
};

type StateFeature = Feature<Polygon | MultiPolygon, StateProperties>;

let cachedStates: FeatureCollection<Polygon | MultiPolygon, StateProperties> | null = null;

export function getStateBoundaries(): FeatureCollection<Polygon | MultiPolygon, StateProperties> {
  if (cachedStates) {
    return cachedStates;
  }

  const topology = usStates as unknown as {
    objects: {
      states: unknown;
    };
  };

  cachedStates = feature(topology as never, topology.objects.states as never) as unknown as FeatureCollection<
    Polygon | MultiPolygon,
    StateProperties
  >;

  return cachedStates;
}

export function getStateLabel(state: StateFeature, fallbackIndex: number): string {
  return state.properties?.name?.trim() || `state-${fallbackIndex + 1}`;
}