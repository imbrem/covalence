import { CovalenceClient } from 'covalence-client';

export const client = new CovalenceClient({
	baseUrl: (import.meta.env.VITE_COV_API_BASE as string | undefined) ?? '',
});
