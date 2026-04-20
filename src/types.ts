import type { FeatureCollection, GeoJsonProperties, Geometry } from 'geojson';

export type AnyFeatureCollection = FeatureCollection<Geometry, GeoJsonProperties>;

export type ImportSummary = {
  featureCount: number;
  polygonCount: number;
};

export type SplitSummary = {
  originalCount: number;
  splitCount: number;
  untouchedCount: number;
};